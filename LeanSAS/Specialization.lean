import Lean
import LeanSAS.Proof

namespace LeanSAS

open Lean Meta

/-- Top-level generated specialization name for a source declaration. -/
def mkTopSpecName (fname : Name) : Name :=
  fname.append `_spec

/-- Pick the declaration name for a specialization. -/
def mkSpecializationName (fname : Name) (hasStaticArg : Bool) : SasM Name := do
  if hasStaticArg then
    freshSpecializationName fname
  else
    pure (mkTopSpecName fname)

/-- Build an application of a generated specialization to its runtime values. -/
def mkSpecializationCall (specName : Name) (levelParams : List Name) (runtimeVals : Array Expr) : Expr :=
  mkAppN (.const specName (levelParams.map Level.param)) runtimeVals

/-- Reuse an already generated specialization and its theorem, if present. -/
def mkExistingSpecializationResult
    (specName : Name) (levelParams : List Name) (runtimeVals : Array Expr) : SasM Simp.Result := do
  let thmName := specName.append `eq_thm
  let proof? ←
    if (← getEnv).contains thmName then
      -- The theorem proves spec = original, but Simp wants original = spec.
      let thmApp := mkSpecializationCall thmName levelParams runtimeVals
      some <$> mkEqSymm thmApp
    else
      pure none
  return { expr := mkSpecializationCall specName levelParams runtimeVals, proof? }

/-- Add the generated specialization definition to the environment. -/
def addSpecializationDef (specName : Name) (levelParams : List Name) (value : Expr) : SasM Unit := do
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

/--
Add the equality theorem for a generated specialization.

The theorem proves `spec args = original args`. The returned proof is symmetrized
for use as a `Simp.Result` proof, which needs `original args = spec args`.
-/
def addSpecializationTheorem?
    (specName fname : Name) (lvls : List Level) (levelParams : List Name)
    (runtimeVars runtimeVals bodyArgs : Array Expr) (bodyResult : Simp.Result) : SasM (Option Expr) := do
  let thmName := specName.append `eq_thm
  try
    let lvlParams := levelParams.map Level.param
    let fn := Expr.const fname lvls
    let lhs := mkAppN (.const specName lvlParams) runtimeVars
    let rhs := mkAppN fn bodyArgs
    let eq ← mkEq lhs rhs
    let thmType ← mkForallFVars runtimeVars eq
    let proof ←
      if let some bodyProof := bodyResult.proof? then
        mkEqSymm bodyProof
      else
        unless ← isDefEq lhs rhs do
          trace[LeanSAS.sas] "missing transformation proof; trying definitional theorem proof anyway\nleft:{indentExpr lhs}\nright:{indentExpr rhs}"
        mkProofByDefEq lhs
    let finalProof ← mkLambdaFVars runtimeVars proof >>= instantiateMVars
    addAndCompile <| .thmDecl {
      name := thmName
      levelParams := levelParams,
      type := thmType,
      value := finalProof
    }
    trace[LeanSAS.sas] "generated equality theorem {thmName}"
    let thmApp := mkAppN (.const thmName lvlParams) runtimeVals
    some <$> mkEqSymm thmApp
  catch e =>
    trace[LeanSAS.sas] "failed to generate equality theorem: {e.toMessageData}"
    pure none

end LeanSAS
