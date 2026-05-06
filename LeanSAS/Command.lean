import Lean
import LeanSAS.Main

namespace LeanSAS

open Lean Elab Command Meta

/-- Specialize the declaration named `fname` and emit trace output. -/
def elabSasConst (fname : Name) : CommandElabM Unit := do
  liftTermElabM do
    let (specName, generated) ← specializeConst fname
    trace[LeanSAS.sas] "generated {specName}"
    unless generated.isEmpty do
      trace[LeanSAS.sas] "callees: {generated}"

/--
Identifier form of `#sas`.

This is the preferred form for polymorphic definitions and definitions with
implicit typeclass arguments. It resolves the identifier as a declaration name
without elaborating it as a term, so no implicit arguments or instances have to
be synthesized just to select the declaration.
-/
elab "#sas " id:ident : command => do
  let fname ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  elabSasConst fname

end LeanSAS
