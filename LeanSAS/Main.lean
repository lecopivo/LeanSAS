import Lean
import LeanSAS.Types

namespace LeanSAS

open Lean Meta

/-- Top-level generated specialization name for a source declaration. -/
def mkTopSpecName (fname : Name) : Name :=
  fname.append `_spec

/--
Transform an expression by simplifying it and recursively specializing calls.

The transformer is deliberately conservative in v1:

* type-level expressions, propositions, and typeclass instances are left alone;
* calls outside the top-level declaration's root namespace are treated as opaque;
* user-defined callees are either rewritten to same-arity `._spec` definitions or
  to fresh `_sas_N` definitions when static arguments are baked in.
-/
partial def transform (e : Expr) : SasM Expr := do
  unless ← consumeFuel do
    return e
  let type ← inferType e
  if type.isSort then return e
  if (← isClass? type).isSome then return e
  if (← inferType type).isProp then return e
  let e ← simplify e
  match e with
  | .app .. => transformApp e
  | .lam .. =>
      lambdaTelescope e fun xs body => do
        let body ← transform body
        mkLambdaFVars xs body
  | .letE n _t v b _nondep =>
      let v ← transform v
      withLetDecl n (← inferType v) v fun x => do
        let b ← transform (b.instantiate1 x)
        mkLetFVars #[x] b (generalizeNondepLet := false)
  | .proj _ _ s =>
      let s ← transform s
      let e := e.updateProj! s
      return (← reduceProj? e).getD e
  | .mdata _ b => transform b
  | _ => pure e
where
  /-- Run `simp` on `e`, skipping forms where simplification is likely to erase structure. -/
  simplify (e : Expr) : SasM Expr := do
    if e.isFVar || e.isLet || e.isForall then
      return e
    let r ← Simp.simp e
    if r.expr != e then
      trace[LeanSAS.sas.simp] "simplified:{indentExpr e}\n==>{indentExpr r.expr}\n"
    return r.expr

  /-- Transform an application, possibly replacing it by a generated specialization call. -/
  transformApp (e : Expr) : SasM Expr := do
    let (fn, args) := e.withApp fun fn args => (fn, args)
    if let some (fname, _) := fn.const? then
      if fname.getRoot != (← read).root then
        return e
    let args ← args.mapM transform
    let e := mkAppN fn args
    if let some (fname, lvls) := fn.const? then
      if ← shouldSpecialize fname then
        return ← specializeCall fname lvls args
    return e

  /-- Decide whether a constant is a safe recursive-specialization target. -/
  shouldSpecialize (fname : Name) : SasM Bool := do
    if fname.getRoot != (← read).root then return false
    if (toString fname).contains "._spec" then return false
    if (toString fname).contains "_sas_" then return false
    if fname == ``ite then return false
    if fname == ``dite then return false
    if fname == ``bind then return false
    if fname == ``pure then return false
    if ← isRecursiveDefinition fname then return false
    if ← isMatcher fname then return false
    let .defnInfo _ ← getConstInfo fname | return false
    if let some info ← getProjectionFnInfo? fname then
      return info.fromClass
    return true

  /--
  Generate or reuse a specialization for the call `fname args`.

  Arguments containing free variables become parameters of the generated
  specialization. Arguments without free variables are baked into the generated
  body. If no arguments are baked in, the generated name is `fname._spec`; if at
  least one argument is baked in, a fresh `fname_sas_N` name is used.
  -/
  specializeCall (fname : Name) (lvls : List Level) (args : Array Expr) : SasM Expr := do
    let fn := Expr.const fname lvls
    let mut runtimeDecls : Array (Name × Expr) := #[]
    let mut runtimeVals : Array Expr := #[]
    let mut bodyArgs : Array Expr := #[]
    for arg in args do
      if arg.hasFVar then
        let t ← inferType arg
        runtimeDecls := runtimeDecls.push (`x, t)
        runtimeVals := runtimeVals.push arg
      else
        bodyArgs := bodyArgs.push arg

    withLocalDeclsD runtimeDecls fun runtimeVars => do
      let mut j := 0
      let mut bodyArgs := #[]
      for arg in args do
        if arg.hasFVar then
          bodyArgs := bodyArgs.push runtimeVars[j]!
          j := j + 1
        else
          bodyArgs := bodyArgs.push arg

      let hasStaticArg := args.any (fun arg => !arg.hasFVar)
      let specName ←
        if hasStaticArg then
          freshSpecializationName fname
        else
          pure (mkTopSpecName fname)
      if (← getEnv).contains specName then
        return mkAppN (.const specName []) runtimeVals
      let rawBody := mkAppN fn bodyArgs
      let unfolded ← unfoldDefinition rawBody fname
      let body ← transform unfolded
      let value ← mkLambdaFVars runtimeVars body >>= instantiateMVars
      unless ← isTypeCorrect value do
        throwError m!"generated specialization is not type correct:{indentExpr value}"
      let type ← inferType value
      addAndCompile <| .defnDecl {
        name := specName
        levelParams := [],
        type := type,
        value := value,
        hints := .regular value.approxDepth,
        safety := .safe
      }
      recordGenerated specName
      trace[LeanSAS.sas] "generated {specName}:{indentExpr value}"
      return mkAppN (.const specName []) runtimeVals

  /-- Try to unfold `fname` in `e`; leave `e` unchanged if unfolding fails. -/
  unfoldDefinition (e : Expr) (fname : Name) : SasM Expr := do
    try
      return (← unfold e fname).expr
    catch _ =>
      return e

/--
Specialize the definition named `fname` using an elaborated simplifier specification.

This is the lower-level entry point used by the command elaborator after parsing
`simp`-style configuration and arguments.
-/
def specializeConstWith (fname : Name) (simpSpec : SimpSpec) : MetaM (Name × Array Name) := do
  let .defnInfo info ← getConstInfo fname
    | throwError "#sas expects a definition, got {fname}"
  if ← isRecursiveDefinition fname then
    throwError "#sas does not specialize recursive definitions yet: {fname}"
  let specName := mkTopSpecName fname
  if (← getEnv).contains specName then
    throwError "generated declaration already exists: {specName}"

  let lvls := info.levelParams.map Level.param
  let fn := Expr.const fname lvls
  let (value, state) ← runSasMWith fname.getRoot (do
    let value ← forallTelescope info.type fun xs _ => do
      let rawBody ←
        try
          pure (← unfold (mkAppN fn xs) fname).expr
        catch _ =>
          pure (mkAppN fn xs)
      let body ← transform rawBody
      mkLambdaFVars xs body >>= instantiateMVars
    pure value) simpSpec

  unless ← isTypeCorrect value do
    throwError m!"generated top-level specialization is not type correct:{indentExpr value}"
  let type ← inferType value
  addAndCompile <| .defnDecl {
    name := specName
    levelParams := info.levelParams,
    type := type,
    value := value,
    hints := .regular value.approxDepth,
    safety := .safe
  }
  return (specName, state.generated)

/--
Specialize the definition named `fname` and add `fname._spec` to the environment.

Returns the top-level generated name together with generated callee
specializations. This is the implementation behind `#sas`.
-/
def specializeConst (fname : Name) (attrs : Array Name := #[`simp])
    (config : Simp.Config := { zeta := false, zetaDelta := false, iota := true }) : MetaM (Name × Array Name) := do
  let simpTheorems ← attrs.mapM getSimpTheoremsFor
  let simprocs ← attrs.mapM getSimprocsFor
  specializeConstWith fname { config, simpTheorems, simprocs }

end LeanSAS
