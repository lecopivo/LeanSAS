import Lean
import LeanSAS.Types

namespace LeanSAS

open Lean Meta

/-- Fully classified arguments for one generated specialization. -/
structure SpecializedArgs where
  /-- Runtime parameters introduced for the generated specialization. -/
  runtimeVars : Array Expr
  /-- Original values supplied at the call site for `runtimeVars`. -/
  runtimeVals : Array Expr
  /-- Arguments used in the generated specialization body. -/
  bodyArgs : Array Expr
  /-- Whether at least one source argument was baked into the specialization. -/
  hasStaticArg : Bool

/-- Find an already registered runtime value, using fvar identity before defeq. -/
def findRuntimeVal? (vals : Array Expr) (val : Expr) : SasM (Option Nat) := do
  let val := val.consumeMData
  for i in [:vals.size] do
    let other := vals[i]!.consumeMData
    if other.fvarId? == val.fvarId? && val.fvarId?.isSome then
      return some i
    if ← isDefEq other val then
      return some i
  return none

/-- Captured free variables in local-context order. -/
def collectLambdaCaptures (arg : Expr) : SasM (Array Expr) := do
  let lctx ← getLCtx
  let fvarIds := lctx.sortFVarsByContextOrder (collectFVars {} arg).fvarIds
  return fvarIds.map Expr.fvar

/--
Classify source call arguments for specialization.

Regular runtime-dependent arguments remain runtime parameters. Lambda arguments
are static templates, but their captured free variables are extracted as
deduplicated runtime parameters.
-/
def withSpecializedArgs {α}
    (args : Array Expr) (k : SpecializedArgs → SasM α) : SasM α := do
  let mut runtimeDecls : Array (Name × Expr) := #[]
  let mut runtimeVals : Array Expr := #[]
  let mut runtimeArgIdx : Array (Option Nat) := #[]

  for arg in args do
    let argView := arg.consumeMData
    if argView.isLambda then
      for capture in (← collectLambdaCaptures argView) do
        let capture := capture.consumeMData
        if (← findRuntimeVal? runtimeVals capture).isNone then
          let t ← inferType capture
          runtimeDecls := runtimeDecls.push (`x, t)
          runtimeVals := runtimeVals.push capture
      runtimeArgIdx := runtimeArgIdx.push none
    else if argView.hasFVar then
      let idx ←
        if let some i ← findRuntimeVal? runtimeVals argView then
          pure i
        else
          let t ← inferType argView
          let i := runtimeVals.size
          runtimeDecls := runtimeDecls.push (`x, t)
          runtimeVals := runtimeVals.push argView
          pure i
      runtimeArgIdx := runtimeArgIdx.push (some idx)
    else
      runtimeArgIdx := runtimeArgIdx.push none

  withLocalDeclsD runtimeDecls fun runtimeVars => do
    let mut bodyArgs := #[]
    for i in [:args.size] do
      let arg := args[i]!
      if let some j := runtimeArgIdx[i]! then
        bodyArgs := bodyArgs.push runtimeVars[j]!
      else
        bodyArgs := bodyArgs.push (arg.replaceFVars runtimeVals runtimeVars)

    let hasStaticArg := Id.run do
      for arg in args do
        let arg := arg.consumeMData
        if !arg.hasFVar || arg.isLambda then
          return true
      return false

    k { runtimeVars, runtimeVals, bodyArgs, hasStaticArg }

end LeanSAS
