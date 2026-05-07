import Lean
import LeanSAS.Types
import LeanSAS.Proof
import LeanSAS.SpecializeArgs
import LeanSAS.Specialization
import LeanSAS.TransformUtil

namespace LeanSAS

open Lean Meta

mutual

/--
Core logic for generating a specialized function.

Given a function name, level parameters, runtime variables and their corresponding values,
and body arguments (with static args baked in), generates a specialized definition and
its equality theorem.

This function expects to be called WITHIN a `withLocalDeclsD runtimeDecls` context
where the runtimeVars are already bound.

Returns the specialized function call and optionally a proof term.
-/
partial def mkSpecializationCore
    (fname : Name) (lvls : List Level) (levelParams : List Name)
    (runtimeVars : Array Expr) (runtimeVals : Array Expr)
    (bodyArgs : Array Expr) (hasStaticArg : Bool) : SasM Simp.Result := do
  let fn := Expr.const fname lvls
  let specName ← mkSpecializationName fname hasStaticArg
  if (← getEnv).contains specName then
    return (← mkExistingSpecializationResult specName levelParams runtimeVals)

  let rawBody := mkAppN fn bodyArgs
  let unfolded ← unfoldDefinition rawBody fname
  let bodyResult ← transform unfolded
  let value ← mkLambdaFVars runtimeVars bodyResult.expr >>= instantiateMVars
  addSpecializationDef specName levelParams value
  let proof? ← addSpecializationTheorem? specName fname lvls levelParams runtimeVars runtimeVals bodyArgs bodyResult
  return { expr := mkSpecializationCall specName levelParams runtimeVals, proof? }

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
  if let some shared := shareNonlinearBeta? e then
    let proof ← mkEqRefl e
    return (← SimpResult.trans { expr := shared, proof? := some proof } (← transform shared))
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
  | .proj structName idx s =>
      let sResult ← transform s
      let e' := r.expr.updateProj! sResult.expr
      let reduced := (← reduceProj? e').getD e'
      let projProof? ←
        if let some sProof := sResult.proof? then
          mkProjTransformProof? structName idx s sProof
        else
          pure none
      let reduceProof? ←
        if reduced != e' then
          some <$> mkProofByDefEq e'
        else
          pure none
      let proof? ← composeEqProofs r.proof? (← composeEqProofs projProof? reduceProof?)
      return { expr := reduced, proof? }
  | .mdata _ b => transform b
  | _ => pure r

/-- Transform an application, possibly replacing it by a generated specialization call. -/
partial def transformApp (e : Expr) : SasM Simp.Result := do
  let (fn, args) := e.withApp fun fn args => (fn, args)
  if let some (fname, _) := fn.const? then
    if fname.getRoot != (← read).root then
      return { expr := e }
  let argResults ← args.mapM transform
  let args' := argResults.map (·.expr)
  let e' := mkAppN fn args'
  let argProof? ← mkAppArgCongrProof? fn args argResults
  if let some (fname, lvls) := fn.const? then
    if ← shouldSpecialize fname then
      let specResult ← specializeCall fname lvls args'
      return { expr := specResult.expr, proof? := (← composeEqProofs argProof? specResult.proof?) }
  return { expr := e', proof? := argProof? }

/--
Generate or reuse a specialization for the call `fname args`.

Arguments containing free variables become parameters of the generated
specialization. Arguments without free variables are baked into the generated
body. If no arguments are baked in, the generated name is `fname._spec`; if at
least one argument is baked in, a fresh `fname_sas_N` name is used.

Returns both the specialized call expression and a proof that it equals the
original call (when available).
-/
partial def specializeCall (fname : Name) (lvls : List Level) (args : Array Expr) : SasM Simp.Result := do
  withSpecializedArgs args fun s =>
    mkSpecializationCore fname lvls (collectLevelParams lvls) s.runtimeVars s.runtimeVals s.bodyArgs s.hasStaticArg

end

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

  let (_, state) ← runSasMWith fname.getRoot (do
    forallTelescope info.type fun xs _ => do
      -- All arguments are runtime parameters (no static args for top-level specialization)
      let runtimeVars := xs
      let runtimeVals := xs
      let bodyArgs := xs
      let hasStaticArg := false

      -- xs already provides the withLocalDeclsD context we need
      let _result ← mkSpecializationCore fname lvls info.levelParams runtimeVars runtimeVals bodyArgs hasStaticArg
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
