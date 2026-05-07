import Lean
import LeanSAS.Types

namespace LeanSAS

open Lean Meta

/-- Run `simp` on `e`, skipping forms where simplification is likely to erase structure. -/
def simplify (e : Expr) : SasM Simp.Result := do
  if e.isFVar || e.isLet || e.isForall then
    return { expr := e }
  let r ← Simp.simp e
  if r.expr != e then
    trace[LeanSAS.sas.simp] "simplified:{indentExpr e}\n==>{indentExpr r.expr}\n"
  return r

/-- Decide whether a constant is a safe recursive-specialization target. -/
def shouldSpecialize (fname : Name) : SasM Bool := do
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

/-- Try to unfold `fname` in `e`; leave `e` unchanged if unfolding fails. -/
def unfoldDefinition (e : Expr) (fname : Name) : SasM Expr := do
  try
    return (← unfold e fname).expr
  catch _ =>
    return e

end LeanSAS
