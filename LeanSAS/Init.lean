import Lean

open Lean

namespace LeanSAS

/-- Main trace class for specialization decisions and generated declarations. -/
initialize registerTraceClass `LeanSAS.sas

/-- Trace class for expressions changed by the simplifier during specialization. -/
initialize registerTraceClass `LeanSAS.sas.simp

end LeanSAS
