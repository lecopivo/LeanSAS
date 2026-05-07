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
  -- Compose two `Eq` proofs (handling `none`).
  let composeEq (p1 p2 : Option Expr) : MetaM (Option Expr) := do
    match p1, p2 with
    | none, p => pure p
    | p, none => pure p
    | some p1, some p2 => some <$> mkEqTrans p1 p2
  match r.expr with
  | .app .. =>
      let r' ← transformApp r.expr
      let proof? ← composeEq r.proof? r'.proof?
      return { expr := r'.expr, proof? := proof? }
  | .lam .. =>
      lambdaTelescope r.expr fun xs body => do
        let bodyResult ← transform body
        let lam ← mkLambdaFVars xs bodyResult.expr

        -- Build lambda congruence proof using function extensionality
        -- (fun xs => body) = (fun xs => body') if ∀ xs, body = body'
        let proof? : Option Expr ← do
          match r.proof?, bodyResult.proof? with
          | some simpProof, some bodyProof =>
            -- Both simplification and transformation occurred
            -- Compose: e = r.expr (simpProof) and r.expr = lam (by funext bodyProof)
            try
              let bodyProofLam ← mkLambdaFVars xs bodyProof
              let lamProof ← mkFunExt bodyProofLam
              some <$> mkEqTrans simpProof lamProof
            catch e =>
              trace[LeanSAS.sas] "lambda congruence (both) failed: {e.toMessageData}"
              pure none
          | some simpProof, none =>
            -- Only simplification, no body transformation
            pure (some simpProof)
          | none, some bodyProof =>
            -- Only body transformation, use funext
            try
              let bodyProofLam ← mkLambdaFVars xs bodyProof
              some <$> mkFunExt bodyProofLam
            catch e =>
              trace[LeanSAS.sas] "lambda congruence (body) failed: {e.toMessageData}"
              pure none
          | none, none =>
            pure none
        return { expr := lam, proof? := proof? }
  | .letE n _t v b _nondep =>
      let vResult ← transform v
      let xType ← inferType vResult.expr
      withLetDecl n xType vResult.expr fun x => do
        let bResult ← transform (b.instantiate1 x)
        let letExpr ← mkLetFVars #[x] bResult.expr (generalizeNondepLet := false)

        -- Build `fun x => body` over the let-bound fvar `x`. We can't use
        -- `mkLambdaFVars` because it abstracts let-bound fvars as `let`
        -- bindings, not lambdas — but the congruence lemmas need real lambdas.
        let mkLamOverX (body : Expr) : MetaM Expr := do
          let absBody := body.abstract #[x]
          return .lam n xType absBody .default

        -- Let congruence via beta/zeta defeq:
        --   `let x := v in b` ≡ `(fun x => b) v`
        let proof? : Option Expr ← do
          match vResult.proof?, bResult.proof? with
          | some vProof, some bProof =>
            try
              let bProofLam ← mkLamOverX bProof
              let funEqProof ← mkFunExt bProofLam
              let fullProof ← mkCongr funEqProof vProof
              pure (some fullProof)
            catch e =>
              trace[LeanSAS.sas] "let congruence (both) failed: {e.toMessageData}"
              pure none
          | some vProof, none =>
            try
              let bodyFn ← mkLamOverX (b.instantiate1 x)
              let proof ← mkCongrArg bodyFn vProof
              pure (some proof)
            catch e =>
              trace[LeanSAS.sas] "let congruence (value) failed: {e.toMessageData}"
              pure none
          | none, some bProof =>
            try
              let bProofLam ← mkLamOverX bProof
              let funEqProof ← mkFunExt bProofLam
              let proof ← mkCongrFun funEqProof v
              pure (some proof)
            catch e =>
              trace[LeanSAS.sas] "let congruence (body) failed: {e.toMessageData}"
              pure none
          | none, none =>
            pure none
        return { expr := letExpr, proof? := proof? }
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
