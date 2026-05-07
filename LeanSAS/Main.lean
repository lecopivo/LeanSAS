import Lean
import LeanSAS.Types

namespace LeanSAS

open Lean Meta

/-- Top-level generated specialization name for a source declaration. -/
def mkTopSpecName (fname : Name) : Name :=
  fname.append `_spec

/--
Build a proof that `lhs = rhs` given that they are definitionally equal.
This is just `Eq.refl lhs`, but the kernel will check defeq.
-/
def mkProofByDefEq (lhs : Expr) : MetaM Expr := do
  mkEqRefl lhs

/-- Compose two optional equality proofs, treating missing proofs as reflexive steps. -/
def composeEqProofs (p1 p2 : Option Expr) : MetaM (Option Expr) := do
  match p1, p2 with
  | none, p => pure p
  | p, none => pure p
  | some p1, some p2 => some <$> mkEqTrans p1 p2

namespace SimpResult

/-- Compose two consecutive simplification/specialization results. -/
def trans (r1 r2 : Simp.Result) : MetaM Simp.Result := do
  return { expr := r2.expr, proof? := (← composeEqProofs r1.proof? r2.proof?) }

/-- Replace a result's expression and append an optional equality proof for the replacement. -/
def transExpr (r : Simp.Result) (expr : Expr) (proof? : Option Expr) : MetaM Simp.Result := do
  return { expr, proof? := (← composeEqProofs r.proof? proof?) }

end SimpResult

/-- Run proof-producing code conservatively: log failures and continue without a proof. -/
def tryMkProof? (where_ : String) (x : MetaM Expr) : SasM (Option Expr) := do
  try
    some <$> x
  catch e =>
    trace[LeanSAS.sas] "{where_} failed: {e.toMessageData}"
    pure none

/-- Turn a body equality proof into a lambda equality proof using function extensionality. -/
def mkLambdaCongrProof? (where_ : String) (xs : Array Expr) (bodyProof : Expr) : SasM (Option Expr) :=
  tryMkProof? where_ do
    let bodyProofLam ← mkLambdaFVars xs bodyProof
    mkFunExt bodyProofLam

/-- Compose the proof from pre-simplifying a lambda with the proof from transforming its body. -/
def mkLambdaTransformProof? (xs : Array Expr) (simpProof? bodyProof? : Option Expr) : SasM (Option Expr) := do
  match simpProof?, bodyProof? with
  | some simpProof, some bodyProof =>
    let lamProof? ← mkLambdaCongrProof? "lambda congruence" xs bodyProof
    composeEqProofs (some simpProof) lamProof?
  | some simpProof, none =>
    pure (some simpProof)
  | none, some bodyProof =>
    mkLambdaCongrProof? "lambda congruence" xs bodyProof
  | none, none =>
    pure none

/-- Build a real lambda over a let-bound fvar; `mkLambdaFVars` would rebuild a let. -/
def mkLambdaOverLetFVar (n : Name) (xType x body : Expr) : MetaM Expr := do
  let absBody := body.abstract #[x]
  return .lam n xType absBody .default

/--
Build the congruence proof for transforming a let value and/or let body.

The proof uses the definitionally equal view `let x := v; b` as `(fun x => b) v`.
-/
def mkLetTransformProof?
    (n : Name) (xType x originalValue originalBody : Expr)
    (valueProof? bodyProof? : Option Expr) : SasM (Option Expr) := do
  match valueProof?, bodyProof? with
  | some valueProof, some bodyProof =>
    tryMkProof? "let congruence" do
      let bodyProofLam ← mkLambdaOverLetFVar n xType x bodyProof
      let funEqProof ← mkFunExt bodyProofLam
      mkCongr funEqProof valueProof
  | some valueProof, none =>
    tryMkProof? "let value congruence" do
      let bodyFn ← mkLambdaOverLetFVar n xType x originalBody
      mkCongrArg bodyFn valueProof
  | none, some bodyProof =>
    tryMkProof? "let body congruence" do
      let bodyProofLam ← mkLambdaOverLetFVar n xType x bodyProof
      let funEqProof ← mkFunExt bodyProofLam
      mkCongrFun funEqProof originalValue
  | none, none =>
    pure none

/--
Core logic for generating a specialized function.

Given a function name, level parameters, runtime variables and their corresponding values,
and body arguments (with static args baked in), generates a specialized definition and
its equality theorem.

This function expects to be called WITHIN a `withLocalDeclsD runtimeDecls` context
where the runtimeVars are already bound.

Returns the specialized function call and optionally a proof term.
-/
def mkSpecializationCore
    (fname : Name) (lvls : List Level) (levelParams : List Name)
    (runtimeVars : Array Expr) (runtimeVals : Array Expr)
    (bodyArgs : Array Expr) (hasStaticArg : Bool)
    (transform : Expr → SasM Simp.Result)
    (unfoldDefinition : Expr → Name → SasM Expr) : SasM Simp.Result := do
  let fn := Expr.const fname lvls

  let specName ←
    if hasStaticArg then
      freshSpecializationName fname
    else
      pure (mkTopSpecName fname)

  if (← getEnv).contains specName then
    -- If the specialization already exists, check if theorem exists too
    let thmName := specName.append `eq_thm
    let lvlParams := levelParams.map Level.param
    let proof? ←
      if (← getEnv).contains thmName then
        -- The theorem proves spec = original, but Simp wants original = spec
        let thmApp := mkAppN (.const thmName lvlParams) runtimeVals
        some <$> mkEqSymm thmApp
      else
        pure none
    return { expr := mkAppN (.const specName lvlParams) runtimeVals, proof? := proof? }

  let rawBody := mkAppN fn bodyArgs
  let unfolded ← unfoldDefinition rawBody fname
  let bodyResult ← transform unfolded
  let value ← mkLambdaFVars runtimeVars bodyResult.expr >>= instantiateMVars
  unless ← isTypeCorrect value do
    throwError m!"generated specialization is not type correct:{indentExpr value}"
  let type ← inferType value
  addAndCompile <| .defnDecl {
    name := specName
    levelParams := levelParams,
    type := type,
    value := value,
    hints := .regular value.approxDepth,
    safety := .safe
  }
  recordGenerated specName
  trace[LeanSAS.sas] "generated {specName}:{indentExpr value}"

  -- Always generate equality theorem for this specialization
  -- The theorem states: ∀ runtime args, specName runtime_args = fname all_args
  -- i.e., specialized call = original call (without unfolding)
  let thmName := specName.append `eq_thm
  let thmProof? ← try
    let lvlParams := levelParams.map Level.param

    -- Build theorem type: specName runtimeVars = fname bodyArgs
    let lhs := mkAppN (.const specName lvlParams) runtimeVars
    let rhs := mkAppN fn bodyArgs
    let eq ← mkEq lhs rhs
    let thmType ← mkForallFVars runtimeVars eq

    -- Build the proof
    -- We need to prove: lhs = rhs where
    -- - lhs = specName runtimeVars ≡ bodyResult.expr (by definition)
    -- - rhs = fname bodyArgs ≡ unfolded (by unfolding)
    -- - bodyResult.proof?: unfolded = bodyResult.expr (if transformation occurred)
    --
    -- Strategy:
    -- 1. If bodyResult.proof? exists: use Eq.symm to get bodyResult.expr = unfolded
    -- 2. Use definitional equality: lhs ≡ bodyResult.expr and rhs ≡ unfolded
    -- 3. The kernel accepts the proof via defeq
    let proof ←
      if let some bodyProof := bodyResult.proof? then
        -- bodyProof: unfolded = bodyResult.expr
        -- We need: lhs = rhs where lhs ≡ bodyResult.expr and rhs ≡ unfolded
        -- Use Eq.symm to get: bodyResult.expr = unfolded
        -- The kernel will accept this as lhs = rhs via defeq
        mkEqSymm bodyProof
      else
        -- No transformation, bodyResult.expr ≡ unfolded
        -- So lhs ≡ bodyResult.expr ≡ unfolded ≡ rhs
        mkProofByDefEq lhs

    let finalProof ← mkLambdaFVars runtimeVars proof >>= instantiateMVars

    addAndCompile <| .thmDecl {
      name := thmName
      levelParams := levelParams,
      type := thmType,
      value := finalProof
    }
    trace[LeanSAS.sas] "generated equality theorem {thmName}"
    -- The theorem proves: specName args = fname args (spec = original)
    -- But Simp.Result.proof? should prove: fname args = specName args (original = result)
    -- So we symmetrize when returning it as a Simp proof
    let thmApp := mkAppN (.const thmName lvlParams) runtimeVals
    let simpProof ← mkEqSymm thmApp
    pure (some simpProof)
  catch e =>
    trace[LeanSAS.sas] "failed to generate equality theorem: {e.toMessageData}"
    pure none

  let lvlParams := levelParams.map Level.param
  return { expr := mkAppN (.const specName lvlParams) runtimeVals, proof? := thmProof? }

/--
Transform an expression by simplifying it and recursively specializing calls.

The transformer is deliberately conservative in v1:

* type-level expressions, propositions, and typeclass instances are left alone;
* calls outside the top-level declaration's root namespace are treated as opaque;
* user-defined callees are either rewritten to same-arity `._spec` definitions or
  to fresh `_sas_N` definitions when static arguments are baked in.
-/
partial def transform (e : Expr) : SasM Simp.Result := do
  unless ← consumeFuel do
    return { expr := e }
  let type ← inferType e
  if type.isSort then return { expr := e }
  if (← isClass? type).isSome then return { expr := e }
  if (← inferType type).isProp then return { expr := e }
  let r ← simplify e
  match r.expr with
  | .app .. =>
      let r' ← transformApp r.expr
      SimpResult.trans r r'
  | .lam .. =>
      lambdaTelescope r.expr fun xs body => do
        let bodyResult ← transform body
        let lam ← mkLambdaFVars xs bodyResult.expr
        let proof? ← mkLambdaTransformProof? xs r.proof? bodyResult.proof?
        return { expr := lam, proof? }
  | .letE n _t v b _nondep =>
      let vResult ← transform v
      let xType ← inferType vResult.expr
      withLetDecl n xType vResult.expr fun x => do
        let bResult ← transform (b.instantiate1 x)
        let letExpr ← mkLetFVars #[x] bResult.expr (generalizeNondepLet := false)
        let originalBody := b.instantiate1 x
        let proof? ← mkLetTransformProof? n xType x v originalBody vResult.proof? bResult.proof?
        return { expr := letExpr, proof? }
  | .proj _ _ s =>
      let sResult ← transform s
      let e' := r.expr.updateProj! sResult.expr
      let reduced := (← reduceProj? e').getD e'
      -- Proof combines projection transformation with reduction
      return { expr := reduced, proof? := r.proof? }
  | .mdata _ b => transform b
  | _ => pure r
where
  /-- Run `simp` on `e`, skipping forms where simplification is likely to erase structure. -/
  simplify (e : Expr) : SasM Simp.Result := do
    if e.isFVar || e.isLet || e.isForall then
      return { expr := e }
    let r ← Simp.simp e
    if r.expr != e then
      trace[LeanSAS.sas.simp] "simplified:{indentExpr e}\n==>{indentExpr r.expr}\n"
    return r

  /-- Transform an application, possibly replacing it by a generated specialization call. -/
  transformApp (e : Expr) : SasM Simp.Result := do
    let (fn, args) := e.withApp fun fn args => (fn, args)
    if let some (fname, _) := fn.const? then
      if fname.getRoot != (← read).root then
        return { expr := e }
    let argResults ← args.mapM transform
    let args' := argResults.map (·.expr)
    let e' := mkAppN fn args'
    if let some (fname, lvls) := fn.const? then
      if ← shouldSpecialize fname then
        let specResult ← specializeCall fname lvls args'
        -- TODO: Compose proofs from argument transformations and specialization
        return specResult
    -- Build congruence proof for application if arguments changed
    let hasProof := argResults.any (·.proof?.isSome)
    if hasProof then
      -- For now, return without proof composition (can be enhanced later)
      return { expr := e', proof? := none }
    else
      return { expr := e' }

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

  Returns both the specialized call expression and a proof that it equals the
  original call (when available).
  -/
  specializeCall (fname : Name) (lvls : List Level) (args : Array Expr) : SasM Simp.Result := do
    -- Separate runtime arguments (with FVars) from static arguments (without)
    let mut runtimeDecls : Array (Name × Expr) := #[]
    let mut runtimeVals : Array Expr := #[]
    for arg in args do
      if arg.hasFVar then
        let t ← inferType arg
        runtimeDecls := runtimeDecls.push (`x, t)
        runtimeVals := runtimeVals.push arg

    -- Build bodyArgs with correct interleaving of runtime vars and static values
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
      mkSpecializationCore fname lvls [] runtimeVars runtimeVals bodyArgs hasStaticArg transform unfoldDefinition

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

Also generates an equality theorem `fname._spec.eq_thm` stating that the specialized
version equals the original function.
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

  -- Helper to unfold without access to transform's unfoldDefinition
  let unfoldDef (e : Expr) (name : Name) : SasM Expr := do
    try
      return (← unfold e name).expr
    catch _ =>
      return e

  let (_, state) ← runSasMWith fname.getRoot (do
    forallTelescope info.type fun xs _ => do
      -- All arguments are runtime parameters (no static args for top-level specialization)
      let runtimeVars := xs
      let runtimeVals := xs
      let bodyArgs := xs
      let hasStaticArg := false

      -- xs already provides the withLocalDeclsD context we need
      let _result ← mkSpecializationCore fname lvls info.levelParams runtimeVars runtimeVals bodyArgs hasStaticArg transform unfoldDef
      return ()) simpSpec

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
