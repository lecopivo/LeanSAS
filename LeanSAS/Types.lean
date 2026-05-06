import Lean
import LeanSAS.Init
import LeanSAS.Util

namespace LeanSAS

open Lean Meta

/-- Mutable state threaded through one `#sas` specialization run. -/
structure State where
  /-- Next numeric suffix for fresh `_sas_N` callee-specialization names. -/
  nextId : Nat := 1
  /-- Names of generated callee specializations, reported by the command. -/
  generated : Array Name := #[]
  /-- Conservative traversal budget to prevent accidental non-structural loops. -/
  fuel : Nat := 2000

/-- Read-only context for one specialization run. -/
structure Context where
  /--
  Root namespace/name component of the top-level function being specialized.

  v1 uses this as a conservative filter: only definitions with the same root are
  recursively specialized. This prevents loops through core operations such as
  `Nat.add`, which `simp` may expose and re-normalize back to notation.
  -/
  root : Name

/--
Monad used by the specialization pass.

It combines a small read-only context, mutable generation state, and Lean's
`SimpM`, so the transformer can call the simplifier while adding declarations in
the surrounding `MetaM` environment.
-/
abbrev SasM := ReaderT Context <| StateT State SimpM

/--
Run a `SasM` computation with the requested simp attributes.

The simplifier is configured conservatively: zeta reduction is disabled to avoid
destroying let-sharing, while iota reduction is enabled so simple matches can
compute when `simp` uses them.
-/
def runSasM {α} (root : Name) (x : SasM α) (attrs : Array Name := #[`simp]) : MetaM (α × State) := do
  let simpCtx ← Simp.mkContext
    (config := { zeta := false, zetaDelta := false, iota := true })
    (simpTheorems := ← attrs.mapM getSimpTheoremsFor)
  let simpState : Simp.State := {}
  let simprocs ← attrs.mapM getSimprocsFor
  let simpMethods := Simp.mkDefaultMethodsCore simprocs
  let ((r, s), _) ← (StateT.run (x { root := root }) {}).run simpCtx simpState simpMethods
  return (r, s)

/--
Generate a fresh name for a partial/static-argument specialization of `base`.

The generated name has the form `base_sas_N`. A flat suffix is used instead of a
nested name like `base._spec_N` because nested generated names interacted badly
with Lean's async declaration table during command replay.
-/
def freshSpecializationName (base : Name) : SasM Name := do
  let rec go (fuel : Nat) : SasM Name := do
    match fuel with
    | 0 =>
      throwError "failed to generate fresh specialization name for {base}"
    | fuel + 1 =>
    let id := (← get).nextId
    modify fun s => { s with nextId := id + 1 }
    let name := base.appendAfter s!"_sas_{id}"
    if (← getEnv).contains name then
      go fuel
    else
      return name
  go 10000

/-- Record a generated callee specialization for user-facing command output. -/
def recordGenerated (name : Name) : SasM Unit := do
  modify fun s => { s with generated := s.generated.push name }

/--
Consume one traversal step from the specialization budget.

Returns `false` when the budget is exhausted. The caller should then leave the
current expression unchanged. This is a temporary v1 guard against accidental
loops caused by simplification exposing expressions that normalize back to their
starting form.
-/
def consumeFuel : SasM Bool := do
  let s ← get
  if s.fuel == 0 then
    return false
  modify fun s => { s with fuel := s.fuel - 1 }
  return true

end LeanSAS
