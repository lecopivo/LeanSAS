import LeanSAS

namespace LeanSASTests

def addOne (x : Nat) := x + 1
def useAddOne (n : Nat) := addOne n

#sas useAddOne
/-- info: def LeanSASTests.useAddOne._spec : Nat → Nat :=
fun n => addOne._spec n -/
#guard_msgs in
#print useAddOne._spec
/-- info: def LeanSASTests.addOne._spec : Nat → Nat :=
fun x => x + 1 -/
#guard_msgs in
#print addOne._spec

def scaleAdd (k x : Nat) := k * x + 1
def byTwo (x : Nat) := scaleAdd 2 x

#sas byTwo
/-- info: def LeanSASTests.byTwo._spec : Nat → Nat :=
fun x => scaleAdd_sas_1 x -/
#guard_msgs in
#print byTwo._spec
/-- info: def LeanSASTests.scaleAdd_sas_1 : Nat → Nat :=
fun x => 2 * x + 1 -/
#guard_msgs in
#print scaleAdd_sas_1

def f (a b : Nat) := a + b
def g (x : Nat) := f 10 x
def h (x : Nat) := g (x + 1)

#sas h
/-- info: def LeanSASTests.h._spec : Nat → Nat :=
fun x => g._spec (x + 1) -/
#guard_msgs in
#print h._spec
/--
info: def LeanSASTests.g._spec : Nat → Nat :=
fun x => f_sas_1 x
-/
#guard_msgs in
#print g._spec
/--
info: def LeanSASTests.f_sas_1 : Nat → Nat :=
fun x => 10 + x
-/
#guard_msgs in
#print f_sas_1

def fChain (x : Nat) := x + 1
def gChain (x : Nat) := fChain x
def hChain (x : Nat) := gChain x

#sas hChain
/-- info: def LeanSASTests.hChain._spec : Nat → Nat :=
fun x => gChain._spec x -/
#guard_msgs in
#print hChain._spec
/-- info: def LeanSASTests.gChain._spec : Nat → Nat :=
fun x => fChain._spec x -/
#guard_msgs in
#print gChain._spec
/-- info: def LeanSASTests.fChain._spec : Nat → Nat :=
fun x => x + 1 -/
#guard_msgs in
#print fChain._spec

def addZero (x : Nat) := 0 + x
def useAddZero (x : Nat) := addZero x

#sas useAddZero
/-- info: def LeanSASTests.useAddZero._spec : Nat → Nat :=
fun x => addZero._spec x -/
#guard_msgs in
#print useAddZero._spec
/-- info: def LeanSASTests.addZero._spec : Nat → Nat :=
fun x => x -/
#guard_msgs in
#print addZero._spec

def addWrap (x y : Nat) := x + y

#sas addWrap
/-- info: def LeanSASTests.addWrap._spec : Nat → Nat → Nat :=
fun x y => x + y -/
#guard_msgs in
#print addWrap._spec

def letExample (x : Nat) :=
  let y := 0 + x + 1
  let z := y + (0 + y)
  z + y

#sas (config := { zeta := false }) letExample
/-- info: def LeanSASTests.letExample._spec : Nat → Nat :=
fun x =>
  let y := x + 1;
  let z := y + y;
  z + y -/
#guard_msgs in
#print letExample._spec

def letSpecialize (x : Nat) :=
  let y := x + 1
  let z := scaleAdd 3 y
  z + y

#sas (config := { zeta := false }) letSpecialize
/-- info: def LeanSASTests.letSpecialize._spec : Nat → Nat :=
fun x =>
  let y := x + 1;
  let z := scaleAdd_sas_2 y;
  z + y -/
#guard_msgs in
#print letSpecialize._spec
/-- info: def LeanSASTests.scaleAdd_sas_2 : Nat → Nat :=
fun x => 3 * x + 1 -/
#guard_msgs in
#print scaleAdd_sas_2

def boolNotNot (b : Bool) := !(!b)

#sas boolNotNot
/-- info: def LeanSASTests.boolNotNot._spec : Bool → Bool :=
fun b => b -/
#guard_msgs in
#print boolNotNot._spec

theorem custom_not_not (b : Bool) : !(!b) = b := by
  cases b <;> rfl

def boolNotNotOnly (b : Bool) := !(!b)

#sas only [Bool.not_not] boolNotNotOnly
/-- info: def LeanSASTests.boolNotNotOnly._spec : Bool → Bool :=
fun b => b -/
#guard_msgs in
#print boolNotNotOnly._spec

/-- info: LeanSASTests.boolNotNot._spec.eq_thm (b : Bool) : boolNotNot._spec b = boolNotNot b -/
#guard_msgs in
#check boolNotNot._spec.eq_thm

def boolNotNotNoSimp (b : Bool) := !(!b)

#sas [-Bool.not_not] boolNotNotNoSimp
/-- info: def LeanSASTests.boolNotNotNoSimp._spec : Bool → Bool :=
fun b => !!b -/
#guard_msgs in
#print boolNotNotNoSimp._spec

class SlowEnum (α : Type) where
  elems : List α

class FastEnum (α : Type) [SlowEnum α] where
  fastElems : List α
  fast_eq : SlowEnum.elems (α := α) = fastElems

def univSlow {α : Type} [SlowEnum α] : List α :=
  SlowEnum.elems (α := α)

def univFast {α : Type} [SlowEnum α] [FastEnum α] : List α :=
  FastEnum.fastElems (α := α)

@[simp]
theorem univSlow_eq_univFast {α : Type} [SlowEnum α] [FastEnum α] :
    (univSlow (α := α)) = univFast (α := α) := by
  unfold univSlow univFast
  exact FastEnum.fast_eq (α := α)

inductive Small where
  | a
  | b

instance : SlowEnum Small where
  elems := [Small.a, Small.b]

instance : FastEnum Small where
  fastElems := [Small.a, Small.b]
  fast_eq := rfl

def smallCode : Small → Nat
  | Small.a => 10
  | Small.b => 20

def genericSum {α : Type} [SlowEnum α] (f : α → Nat) : Nat :=
  (univSlow (α := α)).foldl (fun acc x => acc + f x) 0

-- #sas genericSum

def smallSum : Nat :=
  genericSum (α := Small) smallCode

#sas smallSum
/-- info: def LeanSASTests.smallSum._spec : Nat :=
genericSum_sas_1 -/
#guard_msgs in
#print smallSum._spec
/-- info: def LeanSASTests.genericSum_sas_1 : Nat :=
List.foldl (fun acc x => acc + smallCode x) 0 univFast -/
#guard_msgs in
#print genericSum_sas_1

#sas genericSum
/-- info: def LeanSASTests.genericSum._spec : {α : Type} → [SlowEnum α] → (α → Nat) → Nat :=
fun {α} [SlowEnum α] f => List.foldl (fun acc x => acc + f x) 0 univSlow -/
#guard_msgs in
#print genericSum._spec

/-! More involved regression tests for traversal and proof construction. -/

def nestedLetDeep (x : Nat) :=
  let a := 0 + x
  let b := 0 + a + 1
  let c := b + (0 + a)
  c + (0 + b)

#sas (config := { zeta := false }) nestedLetDeep
/--
info: def LeanSASTests.nestedLetDeep._spec : Nat → Nat :=
fun x =>
  let a := x;
  let b := a + 1;
  let c := b + a;
  c + b
-/
#guard_msgs in
#print nestedLetDeep._spec
/-- info: LeanSASTests.nestedLetDeep._spec.eq_thm (x : Nat) : nestedLetDeep._spec x = nestedLetDeep x -/
#guard_msgs in
#check nestedLetDeep._spec.eq_thm

example (x : Nat) : nestedLetDeep._spec x = nestedLetDeep x :=
  nestedLetDeep._spec.eq_thm x

def lambdaCallee (k x : Nat) := k + x

def lambdaTransform (k : Nat) : Nat → Nat :=
  fun x => lambdaCallee (0 + k) (0 + x)

#sas lambdaTransform
/-- info: def LeanSASTests.lambdaTransform._spec : Nat → Nat → Nat :=
fun k a => lambdaCallee._spec k a -/
#guard_msgs in
#print lambdaTransform._spec
/-- info: def LeanSASTests.lambdaCallee._spec : Nat → Nat → Nat :=
fun x x_1 => x + x_1 -/
#guard_msgs in
#print lambdaCallee._spec
/-- info: LeanSASTests.lambdaTransform._spec.eq_thm (k a✝ : Nat) : lambdaTransform._spec k a✝ = lambdaTransform k a✝ -/
#guard_msgs in
#check lambdaTransform._spec.eq_thm

example (k x : Nat) : lambdaTransform._spec k x = lambdaTransform k x :=
  lambdaTransform._spec.eq_thm k x

def appArgCallee (n : Nat) (b : Bool) :=
  if b then n + 1 else n

def appArgTransform (x : Nat) (b : Bool) :=
  appArgCallee (0 + x) (!(!b))

#sas appArgTransform
/-- info: def LeanSASTests.appArgTransform._spec : Nat → Bool → Nat :=
fun x b => appArgCallee._spec x b -/
#guard_msgs in
#print appArgTransform._spec
/-- info: def LeanSASTests.appArgCallee._spec : Nat → Bool → Nat :=
fun x x_1 => if x_1 = true then x + 1 else x -/
#guard_msgs in
#print appArgCallee._spec
/-- info: LeanSASTests.appArgTransform._spec.eq_thm (x : Nat) (b : Bool) : appArgTransform._spec x b = appArgTransform x b -/
#guard_msgs in
#check appArgTransform._spec.eq_thm

example (x : Nat) (b : Bool) : appArgTransform._spec x b = appArgTransform x b :=
  appArgTransform._spec.eq_thm x b

def functionArgCallee (f : Nat → Nat) (x : Nat) :=
  f x

def functionArgTransform (x z : Nat) :=
  functionArgCallee (fun y => 0 + y*z + x) x

#sas functionArgTransform
/-- info: def LeanSASTests.functionArgTransform._spec : Nat → Nat → Nat :=
fun x z => functionArgCallee_sas_1 x z -/
#guard_msgs in
#print functionArgTransform._spec
/-- info: def LeanSASTests.functionArgCallee_sas_1 : Nat → Nat → Nat :=
fun x x_1 => x * x_1 + x -/
#guard_msgs in
#print functionArgCallee_sas_1
/-- info: LeanSASTests.functionArgTransform._spec.eq_thm (x z : Nat) : functionArgTransform._spec x z = functionArgTransform x z -/
#guard_msgs in
#check functionArgTransform._spec.eq_thm

example (x z : Nat) : functionArgTransform._spec x z = functionArgTransform x z :=
  functionArgTransform._spec.eq_thm x z


def functionArg2Callee (f : Nat → Nat → Nat) (x y : Nat) :=
  f (x+y) (x*y)

def functionArg2Transform (x z : Nat) :=
  functionArg2Callee (fun y => Nat.add (0 + y*z + x)) x

#sas functionArg2Transform
/--
info: def LeanSASTests.functionArg2Transform._spec : Nat → Nat → Nat → Nat :=
fun x z y => functionArg2Callee_sas_1 x z y
-/
#guard_msgs in
#print functionArg2Transform._spec

/--
info: def LeanSASTests.functionArg2Callee_sas_1 : Nat → Nat → Nat → Nat :=
fun x x_1 x_2 => (x + x_2) * x_1 + x + x * x_2
-/
#guard_msgs in
#print functionArg2Callee_sas_1

def expensiveInput (x : Nat) :=
  x + 1

def nonlinearFunctionArgCallee (f : Nat → Nat) (x : Nat) :=
  f (expensiveInput x)

def nonlinearFunctionArgTransform (a b x : Nat) :=
  nonlinearFunctionArgCallee (fun y => a * y + b * y) x

#sas (config := { zeta := false }) nonlinearFunctionArgTransform
/--
info: def LeanSASTests.nonlinearFunctionArgTransform._spec : Nat → Nat → Nat → Nat :=
fun a b x => nonlinearFunctionArgCallee_sas_1 a b x
-/
#guard_msgs in
#print nonlinearFunctionArgTransform._spec
/--
info: def LeanSASTests.nonlinearFunctionArgCallee_sas_1 : Nat → Nat → Nat → Nat :=
fun x x_1 x_2 =>
  let y := expensiveInput._spec x_2;
  x * y + x_1 * y
-/
#guard_msgs in
#print nonlinearFunctionArgCallee_sas_1
/--
info: LeanSASTests.nonlinearFunctionArgTransform._spec.eq_thm (a b x : Nat) :
  nonlinearFunctionArgTransform._spec a b x = nonlinearFunctionArgTransform a b x
-/
#guard_msgs in
#check nonlinearFunctionArgTransform._spec.eq_thm

example (a b x : Nat) :
    nonlinearFunctionArgTransform._spec a b x = nonlinearFunctionArgTransform a b x :=
  nonlinearFunctionArgTransform._spec.eq_thm a b x

def captureOrderCallee (n : Nat) (f : Nat → Nat) (m : Nat) :=
  f n + m

def captureOrderTransform (x y z : Nat) :=
  captureOrderCallee z (fun w => x + w + y) x

#sas captureOrderTransform
/-- info: def LeanSASTests.captureOrderTransform._spec : Nat → Nat → Nat → Nat :=
fun x y z => captureOrderCallee_sas_1 z x y -/
#guard_msgs in
#print captureOrderTransform._spec
/-- info: def LeanSASTests.captureOrderCallee_sas_1 : Nat → Nat → Nat → Nat :=
fun x x_1 x_2 => x_1 + x + x_2 + x_1 -/
#guard_msgs in
#print captureOrderCallee_sas_1
/--
info: LeanSASTests.captureOrderTransform._spec.eq_thm (x y z : Nat) :
  captureOrderTransform._spec x y z = captureOrderTransform x y z
-/
#guard_msgs in
#check captureOrderTransform._spec.eq_thm

example (x y z : Nat) : captureOrderTransform._spec x y z = captureOrderTransform x y z :=
  captureOrderTransform._spec.eq_thm x y z

def repeatedCaptureCallee (f : Nat → Nat) (x : Nat) :=
  f x

def repeatedCaptureTransform (a x : Nat) :=
  repeatedCaptureCallee (fun y => a + y + a) x

#sas repeatedCaptureTransform
/-- info: def LeanSASTests.repeatedCaptureTransform._spec : Nat → Nat → Nat :=
fun a x => repeatedCaptureCallee_sas_1 a x -/
#guard_msgs in
#print repeatedCaptureTransform._spec
/-- info: def LeanSASTests.repeatedCaptureCallee_sas_1 : Nat → Nat → Nat :=
fun x x_1 => x + x_1 + x -/
#guard_msgs in
#print repeatedCaptureCallee_sas_1
/--
info: LeanSASTests.repeatedCaptureTransform._spec.eq_thm (a x : Nat) :
  repeatedCaptureTransform._spec a x = repeatedCaptureTransform a x
-/
#guard_msgs in
#check repeatedCaptureTransform._spec.eq_thm

example (a x : Nat) : repeatedCaptureTransform._spec a x = repeatedCaptureTransform a x :=
  repeatedCaptureTransform._spec.eq_thm a x

def cheapBetaCallee (f : Nat → Nat) (x : Nat) :=
  f x

def cheapBetaTransform (a x : Nat) :=
  cheapBetaCallee (fun y => y + y + a) x

#sas (config := { zeta := false }) cheapBetaTransform
/-- info: def LeanSASTests.cheapBetaTransform._spec : Nat → Nat → Nat :=
fun a x => cheapBetaCallee_sas_1 a x -/
#guard_msgs in
#print cheapBetaTransform._spec
/-- info: def LeanSASTests.cheapBetaCallee_sas_1 : Nat → Nat → Nat :=
fun x x_1 => x_1 + x_1 + x -/
#guard_msgs in
#print cheapBetaCallee_sas_1
/-- info: LeanSASTests.cheapBetaTransform._spec.eq_thm (a x : Nat) : cheapBetaTransform._spec a x = cheapBetaTransform a x -/
#guard_msgs in
#check cheapBetaTransform._spec.eq_thm

example (a x : Nat) : cheapBetaTransform._spec a x = cheapBetaTransform a x :=
  cheapBetaTransform._spec.eq_thm a x

def todoArgProducer (x : Nat) :=
  0 + x

def todoArgConsumer (n k : Nat) :=
  n + k

def todoArgumentSpecialization (x : Nat) :=
  todoArgConsumer (todoArgProducer x) 5

#sas todoArgumentSpecialization
/-- info: def LeanSASTests.todoArgumentSpecialization._spec : Nat → Nat :=
fun x => todoArgConsumer_sas_1 (todoArgProducer._spec x) -/
#guard_msgs in
#print todoArgumentSpecialization._spec
/-- info: def LeanSASTests.todoArgProducer._spec : Nat → Nat :=
fun x => x -/
#guard_msgs in
#print todoArgProducer._spec
/-- info: def LeanSASTests.todoArgConsumer_sas_1 : Nat → Nat :=
fun x => x + 5 -/
#guard_msgs in
#print todoArgConsumer_sas_1
/--
info: LeanSASTests.todoArgumentSpecialization._spec.eq_thm (x : Nat) :
  todoArgumentSpecialization._spec x = todoArgumentSpecialization x
-/
#guard_msgs in
#check todoArgumentSpecialization._spec.eq_thm

example (x : Nat) : todoArgumentSpecialization._spec x = todoArgumentSpecialization x :=
  todoArgumentSpecialization._spec.eq_thm x

def affine (a b x : Nat) :=
  a * x + b

def staticUnderLetLambda (x : Nat) :=
  let mk := fun y => affine 4 7 (0 + y)
  let y := 0 + x
  mk y + mk (0 + y)

#sas (config := { zeta := false }) staticUnderLetLambda
/--
info: def LeanSASTests.staticUnderLetLambda._spec : Nat → Nat :=
fun x =>
  let mk := fun y => affine_sas_1 y;
  let y := x;
  mk y + mk y
-/
#guard_msgs in
#print staticUnderLetLambda._spec
/-- info: def LeanSASTests.affine_sas_1 : Nat → Nat :=
fun x => 4 * x + 7 -/
#guard_msgs in
#print affine_sas_1
/-- info: LeanSASTests.staticUnderLetLambda._spec.eq_thm (x : Nat) : staticUnderLetLambda._spec x = staticUnderLetLambda x -/
#guard_msgs in
#check staticUnderLetLambda._spec.eq_thm

example (x : Nat) : staticUnderLetLambda._spec x = staticUnderLetLambda x :=
  staticUnderLetLambda._spec.eq_thm x

structure Pair where
  left : Nat
  right : Nat

def pairScore (p : Pair) :=
  p.left + (0 + p.right)

def projectionTransform (x : Nat) :=
  let p : Pair := { left := 0 + x, right := x + 1 }
  pairScore p + (0 + p.left)

#sas (config := { zeta := false }) projectionTransform
/--
info: def LeanSASTests.projectionTransform._spec : Nat → Nat :=
fun x =>
  let p := { left := x, right := x + 1 };
  pairScore p + p.left
-/
#guard_msgs in
#print projectionTransform._spec
/-- info: LeanSASTests.projectionTransform._spec.eq_thm (x : Nat) : projectionTransform._spec x = projectionTransform x -/
#guard_msgs in
#check projectionTransform._spec.eq_thm

example (x : Nat) : projectionTransform._spec x = projectionTransform x :=
  projectionTransform._spec.eq_thm x

def makePairForProjection (x : Nat) : Pair :=
  { left := 0 + x, right := x + 1 }

def projectionOfTransformedStruct (x : Nat) :=
  (makePairForProjection x).left

#sas projectionOfTransformedStruct
/-- info: def LeanSASTests.projectionOfTransformedStruct._spec : Nat → Nat :=
fun x => (makePairForProjection._spec x).left -/
#guard_msgs in
#print projectionOfTransformedStruct._spec
/-- info: def LeanSASTests.makePairForProjection._spec : Nat → Pair :=
fun x => { left := x, right := x + 1 } -/
#guard_msgs in
#print makePairForProjection._spec
/--
info: LeanSASTests.projectionOfTransformedStruct._spec.eq_thm (x : Nat) :
  projectionOfTransformedStruct._spec x = projectionOfTransformedStruct x
-/
#guard_msgs in
#check projectionOfTransformedStruct._spec.eq_thm

example (x : Nat) :
    projectionOfTransformedStruct._spec x = projectionOfTransformedStruct x :=
  projectionOfTransformedStruct._spec.eq_thm x

def genericFoldMap {α : Type} [SlowEnum α] (offset : Nat) (f : α → Nat) : Nat :=
  ((univSlow (α := α)).map (fun a => 0 + offset + f a)).foldl (fun acc n => acc + n) 0

def smallFoldMap : Nat :=
  genericFoldMap (α := Small) 5 smallCode

#sas smallFoldMap
/-- info: def LeanSASTests.smallFoldMap._spec : Nat :=
genericFoldMap_sas_1 -/
#guard_msgs in
#print smallFoldMap._spec
/-- info: def LeanSASTests.genericFoldMap_sas_1 : Nat :=
List.foldl (fun acc n => acc + n) 0 (List.map (fun a => 5 + smallCode a) univFast) -/
#guard_msgs in
#print genericFoldMap_sas_1
/-- info: LeanSASTests.smallFoldMap._spec.eq_thm : smallFoldMap._spec = smallFoldMap -/
#guard_msgs in
#check smallFoldMap._spec.eq_thm

example : smallFoldMap._spec = smallFoldMap :=
  smallFoldMap._spec.eq_thm

end LeanSASTests

namespace LeanSASExternalTests

def inc (x : Nat) := x + 1

end LeanSASExternalTests

namespace LeanSASTests

def usesExternal (x : Nat) :=
  LeanSASExternalTests.inc (0 + x)

#sas usesExternal
/-- info: def LeanSASTests.usesExternal._spec : Nat → Nat :=
fun x => LeanSASExternalTests.inc x -/
#guard_msgs in
#print usesExternal._spec

def recursiveCount : Nat → Nat
  | 0 => 0
  | n + 1 => recursiveCount n + 1

/-- error: #sas does not specialize recursive definitions yet: LeanSASTests.recursiveCount -/
#guard_msgs in
#sas recursiveCount

def usesRecursiveCallee (x : Nat) :=
  recursiveCount (0 + x)

#sas usesRecursiveCallee
/-- info: def LeanSASTests.usesRecursiveCallee._spec : Nat → Nat :=
fun x => recursiveCount x -/
#guard_msgs in
#print usesRecursiveCallee._spec
/-- info: LeanSASTests.usesRecursiveCallee._spec.eq_thm (x : Nat) : usesRecursiveCallee._spec x = usesRecursiveCallee x -/
#guard_msgs in
#check usesRecursiveCallee._spec.eq_thm

example (x : Nat) : usesRecursiveCallee._spec x = usesRecursiveCallee x :=
  usesRecursiveCallee._spec.eq_thm x

def matchCallee : Nat → Nat
  | 0 => 10
  | n + 1 => addWrap 0 n

def usesMatchCallee (x : Nat) :=
  matchCallee (0 + x)

#sas usesMatchCallee
/-- info: def LeanSASTests.usesMatchCallee._spec : Nat → Nat :=
fun x => matchCallee._spec x -/
#guard_msgs in
#print usesMatchCallee._spec
/--
info: def LeanSASTests.matchCallee._spec : Nat → Nat :=
fun x =>
  match x with
  | 0 => 10
  | n.succ => addWrap_sas_1 n
-/
#guard_msgs in
#print matchCallee._spec
/--
info: def LeanSASTests.addWrap_sas_1 : Nat → Nat :=
fun x => x
-/
#guard_msgs in
#print addWrap_sas_1
/-- info: LeanSASTests.usesMatchCallee._spec.eq_thm (x : Nat) : usesMatchCallee._spec x = usesMatchCallee x -/
#guard_msgs in
#check usesMatchCallee._spec.eq_thm

example (x : Nat) : usesMatchCallee._spec x = usesMatchCallee x :=
  usesMatchCallee._spec.eq_thm x

end LeanSASTests

def main : IO Unit :=
  pure ()
