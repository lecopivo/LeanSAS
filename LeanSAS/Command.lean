import Lean
import Lean.Elab.Tactic.Simp
import LeanSAS.Main

namespace LeanSAS

open Lean Elab Command Meta

namespace Parser

/-- Parser for `#sas`, mirroring the common `simp` grammar. -/
syntax (name := sas) "#sas " Lean.Parser.Tactic.optConfig (&" only")?
  (Lean.Parser.Tactic.simpArgs)? ident : command

end Parser

open Lean.Parser.Tactic

declare_command_config_elab elabSasSimpConfig Simp.Config

/-- Add one simp extension to the current theorem and simproc arrays. -/
private def addSimpExtension (thmArrays : Array SimpTheorems) (simprocs : Array Simprocs)
    (ext₁? : Option SimpExtension) (ext₂? : Option Simp.SimprocExtension) : CommandElabM (Array SimpTheorems × Array Simprocs) := do
  let thmArrays ← match ext₁? with
    | some ext => pure (thmArrays.push (← liftCoreM ext.getTheorems))
    | none => pure thmArrays
  let simprocs ← match ext₂? with
    | some ext => pure (simprocs.push (ext.getState (← getEnv)))
    | none => pure simprocs
  return (thmArrays, simprocs)

/-- Elaborate a single `simp` argument for command-side `#sas` usage. -/
private def elabSimpArg (thms : SimpTheorems) (thmArrays : Array SimpTheorems) (simprocs : Array Simprocs) (arg : Syntax) : CommandElabM (SimpTheorems × Array SimpTheorems × Array Simprocs) := do
  if arg.getKind == ``Lean.Parser.Tactic.simpStar then
    -- There are no local hypotheses in command elaboration.
    return (thms, thmArrays, simprocs)
  else if arg.getKind == ``Lean.Parser.Tactic.simpErase then
    let id := arg[1]
    let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    if ← liftCoreM <| Simp.isSimproc declName then
      return (thms, thmArrays, Simp.SimprocsArray.erase simprocs declName)
    else
      return (← liftTermElabM <| thms.erase (.decl declName), thmArrays, simprocs)
  else if arg.getKind == ``Lean.Parser.Tactic.simpLemma then
    let post := if arg[0].isNone then true else arg[0][0].getKind == ``Lean.Parser.Tactic.simpPost
    let inv := !arg[1].isNone
    let term := arg[2]
    match term with
    | `($id:ident) =>
        let bareName := id.getId.eraseMacroScopes
        if let some ext₁ ← getSimpExtension? bareName then
          let ext₂? ← Simp.getSimprocExtension? bareName
          let (thmArrays, simprocs) ← addSimpExtension thmArrays simprocs (some ext₁) ext₂?
          return (thms, thmArrays, simprocs)
        else if let some ext₂ ← Simp.getSimprocExtension? bareName then
          let (thmArrays, simprocs) ← addSimpExtension thmArrays simprocs none (some ext₂)
          return (thms, thmArrays, simprocs)
        else
          let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
          if ← liftCoreM <| Simp.isSimproc declName then
            return (thms, thmArrays, ← liftCoreM <| Simp.SimprocsArray.add simprocs declName post)
          else
            let info ← getConstInfo declName
            if ← liftTermElabM <| Meta.isProp info.type then
              return (← liftTermElabM <| thms.addConst declName (post := post) (inv := inv), thmArrays, simprocs)
            else
              if inv then
                throwError "invalid `←` modifier: `{declName}` is a declaration to unfold"
              return (← liftTermElabM <| thms.addDeclToUnfold declName, thmArrays, simprocs)
    | _ =>
        let proof ← liftTermElabM <| Term.elabTerm term none
        let proof ← liftTermElabM <| instantiateMVars proof
        let id ← liftTermElabM mkFreshId
        return (← liftTermElabM <| thms.add (.stx id arg) #[] proof (inv := inv) (post := post), thmArrays, simprocs)
  else
    throwUnsupportedSyntax

/-- Elaborate `simp`-style config, `only`, and simp arguments for `#sas`. -/
private def elabSasSimpSpec (cfg : Syntax) (only : Bool) (args? : Option Syntax) : CommandElabM SimpSpec := do
  let config ← elabSasSimpConfig cfg
  let thms0 : SimpTheorems ←
    if only then
      liftTermElabM <| Lean.Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
    else
      liftCoreM getSimpTheorems
  let mut thms := thms0
  let mut thmArrays : Array SimpTheorems := #[]
  let simprocs0 : Array Simprocs ← if only then pure #[] else pure #[← liftCoreM Simp.getSimprocs]
  let mut simprocs := simprocs0
  if let some args := args? then
    for arg in args[1].getSepArgs do
      let (thms', thmArrays', simprocs') ← elabSimpArg thms thmArrays simprocs arg
      thms := thms'
      thmArrays := thmArrays'
      simprocs := simprocs'
  return { config, simpTheorems := #[thms] ++ thmArrays, simprocs }

/-- Specialize the declaration named `fname` and emit trace output. -/
def elabSasConst (fname : Name) (simpSpec : SimpSpec) : CommandElabM Unit := do
  liftTermElabM do
    let (specName, generated) ← specializeConstWith fname simpSpec
    trace[LeanSAS.sas] "generated {specName}"
    unless generated.isEmpty do
      trace[LeanSAS.sas] "callees: {generated}"

elab "#sas " cfg:Lean.Parser.Tactic.optConfig only:(" only")? args:(Lean.Parser.Tactic.simpArgs)? id:ident : command => do
  let fname ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let simpSpec ← elabSasSimpSpec cfg (!only.isNone) args
  elabSasConst fname simpSpec

end LeanSAS
