import Lean
import LeanSAS.Types

namespace LeanSAS

open Lean Meta

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

/-- Build the congruence proof for transforming the structure under a projection. -/
def mkProjTransformProof?
    (structName : Name) (idx : Nat) (structExpr : Expr) (structProof : Expr) : SasM (Option Expr) :=
  tryMkProof? "projection congruence" do
    let structType ← inferType structExpr
    let projFn := Expr.lam `x structType (.proj structName idx (.bvar 0)) .default
    mkCongrArg projFn structProof

/-- Count uses of the de Bruijn variable bound at the current binder depth. -/
partial def countLooseBVarUses (targetDepth : Nat) : Expr → Nat
  | .bvar i => if i == targetDepth then 1 else 0
  | .app f a => countLooseBVarUses targetDepth f + countLooseBVarUses targetDepth a
  | .lam _ t b _ => countLooseBVarUses targetDepth t + countLooseBVarUses (targetDepth + 1) b
  | .forallE _ t b _ => countLooseBVarUses targetDepth t + countLooseBVarUses (targetDepth + 1) b
  | .letE _ t v b _ =>
      countLooseBVarUses targetDepth t + countLooseBVarUses targetDepth v +
        countLooseBVarUses (targetDepth + 1) b
  | .mdata _ b => countLooseBVarUses targetDepth b
  | .proj _ _ s => countLooseBVarUses targetDepth s
  | _ => 0

/-- Arguments that are cheap enough to duplicate or erase during beta reduction. -/
def isCheapBetaArg : Expr → Bool
  | .bvar .. | .fvar .. | .const .. | .sort .. | .lit .. => true
  | .mdata _ e => isCheapBetaArg e
  | _ => false

/--
Rewrite a non-linear lambda application to a let so beta reduction does not
duplicate or erase a nontrivial argument.
-/
def shareNonlinearBeta? (e : Expr) : Option Expr :=
  let (fn, args) := e.withApp fun fn args => (fn.consumeMData, args)
  if h : args.size > 0 then
    match fn with
    | .lam n t b _ =>
        let arg := args[0]
        let uses := countLooseBVarUses 0 b
        if uses == 1 || isCheapBetaArg arg then
          none
        else
          let letExpr := Expr.letE n t arg b false
          some (mkAppN letExpr (args.extract 1 args.size))
    | _ => none
  else
    none

/--
Build an application congruence proof from proofs for transformed arguments.

For each changed argument, this proves the corresponding single-argument step and
then pushes that equality through the remaining original arguments with congruence.
-/
partial def mkAppArgCongrProof? (fn : Expr) (args : Array Expr) (argResults : Array Simp.Result) : SasM (Option Expr) := do
  if !argResults.any (·.proof?.isSome) then
    return none

  let rec liftRemaining (j : Nat) (proof : Expr) : MetaM Expr := do
    if j < args.size then
      liftRemaining (j + 1) (← mkCongrFun proof args[j]!)
    else
      pure proof

  let rec go (i : Nat) (appFn : Expr) (proof? : Option Expr) : MetaM (Option Expr) := do
    if i < args.size then
      let argResult := argResults[i]!
      let proof? ←
        if let some argProof := argResult.proof? then
          let step ← mkCongrArg appFn argProof >>= liftRemaining (i + 1)
          composeEqProofs proof? (some step)
        else
          pure proof?
      go (i + 1) (mkApp appFn argResult.expr) proof?
    else
      pure proof?

  try
    go 0 fn none
  catch e =>
    trace[LeanSAS.sas] "application argument congruence failed: {e.toMessageData}"
    pure none

end LeanSAS
