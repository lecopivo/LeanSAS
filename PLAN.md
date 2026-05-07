# LeanSAS Implementation Plan

This plan tracks the first implementation of LeanSAS: a Lean specialization and simplification pre-pass exposed through the `#sas` command.

The first version intentionally avoids the previous attempt's complex type encoding system. The current goal is to keep the core reliable: specialize functions by baking compile-time-known arguments into generated definitions, recursively specialize callees, simplify generated bodies with `simp`, and maintain equality proofs for generated code.

## Current Status

Implemented:

- `#sas` generates top-level `_spec` definitions.
- Non-recursive same-root callees are recursively specialized.
- Static arguments are baked into fresh `_sas_N` declarations.
- Runtime arguments remain parameters.
- Lambda-valued arguments are specialized as static templates; captured free variables become deduplicated runtime parameters.
- The transformer composes equality proofs through simplification, application argument changes, lambda congruence, let congruence, and specialization theorem reuse.
- Generated specializations get equality theorems when proof construction succeeds.
- Nonlinear beta-redexes with nontrivial arguments are rewritten through `let` to preserve sharing.
- The command supports `simp`-style theorem/configuration selection.
- Tests cover generated declarations with `#print`, theorem types with `#check`, and theorem usability with examples.

## Goals

- Provide a command `#sas f` that creates a generated definition `f._spec`.
- Run `simp` on generated bodies during specialization.
- Recursively specialize non-recursive callees used by `f`.
- Bake arguments known at specialization time into generated definitions.
- Keep runtime arguments as parameters of the generated specialization.
- Generate real Lean declarations, not only log messages.
- Generate equality theorems for generated declarations.
- Keep generated code reasonably sharing-preserving when specializing lambda arguments.
- Keep the implementation independent of HouLean-specific libraries.

## Non-Goals For The First Version

- Do not implement structure/vector/matrix flattening.
- Do not implement general source-argument splitting. Lambda captures are the exception: higher-order specialization may turn one lambda argument into several generated capture parameters.
- Do not implement primitive interpreter evaluation.
- Do not specialize recursive definitions.
- Do not add OpenCL-specific behavior.
- Do not generate unsafe proof-heavy type encoding infrastructure.
- Do not integrate with Lean's compiler pipeline directly yet; start with a command-generated pre-pass.

## Type Encoding Direction

The previous attempt tried to encode some values by splitting structure-like types into multiple arguments. For example, an `Option A` could become two separate generated arguments: one for the value and one for validity.

LeanSAS should use a simpler model when type encodings are added later:

- A type is encoded into another single type.
- A function argument remains one function argument after encoding.
- Example: `Option A` may encode to `A × Bool`, not to two separate arguments `A` and `Bool`.
- Example: a structure may encode to another structure or product-like type, but still occupies one argument slot.

This keeps function arities stable and makes the specialization pass easier to reason about. Type encoding is deferred until after the no-encoding v1 works.

## Proposed Module Layout

- `LeanSAS/Init.lean`
  - Registers trace classes such as `LeanSAS.sas` and `LeanSAS.sas.simp`.

- `LeanSAS/Util.lean`
  - Helper functions for simp extensions and command utilities.

- `LeanSAS/Types.lean`
  - `Context`
  - `State`
  - `SasM := ReaderT Context <| StateT State <| SimpM`
  - `SimpSpec`
  - `runSasMWith` and `runSasM`

- `LeanSAS/Proof.lean`
  - `Simp.Result` composition helpers.
  - Lambda, let, application, and projection congruence proof construction.
  - Sharing-preserving nonlinear beta helpers.

- `LeanSAS/SpecializeArgs.lean`
  - Runtime/static call argument classification.
  - Lambda capture extraction and deduplication.

- `LeanSAS/Specialization.lean`
  - Generated specialization naming.
  - Declaration generation and equality theorem generation.

- `LeanSAS/TransformUtil.lean`
  - Conservative simplification wrapper.
  - Specialization target selection.
  - Definition unfolding helper.

- `LeanSAS/Main.lean`
  - Core expression transformer.
  - Function call specialization.
  - Mutual recursion between transformation and specialization generation.
  - Public specialization entry points.

- `LeanSAS/Command.lean`
  - The `#sas` command.
  - `simp`-style theorem/configuration syntax.

- `Tests/Basic.lean`
  - Small examples and `#guard_msgs` tests.

The root `LeanSAS.lean` imports the command module.

## Core Algorithm

Given a function `f`, `#sas f` should create `f._spec` as follows:

1. Elaborate `f` and inspect its type.
2. Create a lambda over the original runtime parameters of `f`.
3. Transform the body recursively.
4. Run `simp` during transformation.
5. For each application `g a1 ... an`:
   - Recursively transform all arguments.
   - If `g` is a non-recursive definition that should be specialized, classify each argument.
   - Arguments that do not depend on current runtime free variables are compile-time-known and are baked into the generated specialization.
   - Arguments that depend on runtime free variables remain parameters.
   - Lambda arguments are baked in even when they capture free variables; their captures are extracted as deduplicated runtime parameters.
   - Build a generated specialization of `g` over only the remaining runtime arguments.
   - Replace the original call with a call to the generated specialization.
   - Compose the argument-transformation proof with the specialization proof.
6. Generate declarations immediately, recursively transforming generated bodies.
7. Add all generated declarations and equality theorems to the environment.

## First Specialization Rule

For an application:

```lean
g a1 a2 a3
```

where `a1` and `a3` are known at specialization time and `a2` depends on runtime variables, generate a specialization equivalent to:

```lean
def g._spec_N (x2 : T2) :=
  g a1 x2 a3
```

and replace the original call with:

```lean
g._spec_N a2
```

The generated body is then recursively simplified and specialized.

## Lambda Argument Specialization

When a lambda is passed to a specialized callee, LeanSAS treats the lambda as static code. Captured free variables become runtime parameters of the generated callee specialization.

For example:

```lean
def functionArgCallee (f : Nat → Nat) (x : Nat) :=
  f x

def functionArgTransform (x z : Nat) :=
  functionArgCallee (fun y => 0 + y*z + x) x
```

can generate:

```lean
def functionArgTransform._spec : Nat → Nat → Nat :=
  fun x z => functionArgCallee_sas_1 x z

def functionArgCallee_sas_1 : Nat → Nat → Nat :=
  fun x z => x * z + x
```

The capture `x` is not duplicated as a separate parameter when it also appears as an ordinary runtime argument.

## Sharing-Preserving Beta

Lambda specialization can expose beta-redexes. Naive beta reduction can duplicate a nontrivial argument when the lambda parameter is used more than once:

```lean
def nonlinearFunctionArgCallee (f : Nat → Nat) (x : Nat) :=
  f (expensiveInput x)

def nonlinearFunctionArgTransform (a b x : Nat) :=
  nonlinearFunctionArgCallee (fun y => a * y + b * y) x
```

LeanSAS rewrites such redexes through a `let`, preserving sharing:

```lean
fun a b x =>
  let y := expensiveInput._spec x
  a * y + b * y
```

Cheap arguments such as variables and constants may still be duplicated.

## Function Selection

The first version should specialize only conservative targets:

- Definitions, not axioms/theorems/opaque constants.
- Non-recursive definitions.
- Non-matcher definitions.
- No propositions, classes, or type-level values.

The pass should avoid specializing core control-flow constants such as `ite`, `dite`, `bind`, and `pure` until there is a specific implementation for them.

## Name Generation

The top-level generated name should be deterministic:

```lean
f._spec
```

For callees, use deterministic generated names with collision handling, for example:

```lean
g_sas_1
g_sas_2
```

Avoid relying on pretty-printed argument values for names in the first version. Pretty-printed names are useful for debugging but fragile as declaration names.

## Simp Support

The first version should run `simp` with a conservative configuration:

```lean
{ zeta := false, zetaDelta := false, iota := true }
```

The command supports `simp`-style theorem and configuration syntax:

```lean
#sas (config := {...}) only [thm1, thm2] f
```

## Minimal Tests

Start with monomorphic examples using only Lean core types.

```lean
def addOne (x : Nat) := x + 1
def useAddOne (n : Nat) := addOne n

#sas useAddOne
#check useAddOne._spec
```

Known-argument specialization:

```lean
def scaleAdd (k x : Nat) := k * x + 1
def byTwo (x : Nat) := scaleAdd 2 x

#sas byTwo
#check byTwo._spec
```

Nested calls:

```lean
def f (a b : Nat) := a + b
def g (x : Nat) := f 10 x
def h (x : Nat) := g (x + 1)

#sas h
#check h._spec
```

Simp-driven specialization:

```lean
@[simp] theorem zero_add_nat (x : Nat) : 0 + x = x := Nat.zero_add x

def addZero (x : Nat) := 0 + x
def main (x : Nat) := addZero x

#sas main
#check main._spec
```

Higher-order specialization:

```lean
def functionArgCallee (f : Nat → Nat) (x : Nat) := f x
def functionArgTransform (x z : Nat) :=
  functionArgCallee (fun y => 0 + y*z + x) x

#sas functionArgTransform
#print functionArgTransform._spec
#print functionArgCallee_sas_1
#check functionArgTransform._spec.eq_thm
```

Sharing preservation:

```lean
def expensiveInput (x : Nat) := x + 1
def nonlinearFunctionArgCallee (f : Nat → Nat) (x : Nat) := f (expensiveInput x)
def nonlinearFunctionArgTransform (a b x : Nat) :=
  nonlinearFunctionArgCallee (fun y => a * y + b * y) x

#sas (config := { zeta := false }) nonlinearFunctionArgTransform
#print nonlinearFunctionArgCallee_sas_1
#check nonlinearFunctionArgTransform._spec.eq_thm
```

## Milestones

1. Port the minimal monad and simp runner. Done.
2. Implement the recursive expression traversal. Done.
3. Implement call-site specialization. Done.
4. Implement declaration generation for generated specializations. Done.
5. Implement `#sas f` for non-recursive definitions. Done.
6. Add basic and regression tests with guarded generated output. Done.
7. Add equality theorem generation and proof composition API. Done.
8. Add lambda-argument specialization with capture deduplication. Done.
9. Add sharing-preserving nonlinear beta handling. Done.
10. Improve robustness for projections, matches, and dependent cases.
11. Refactor helper APIs out of `LeanSAS/Main.lean` if they continue to grow.
12. Design and implement the later one-type-to-one-type encoding layer.

## Known Risks

- Universe-polymorphic definitions require careful level parameter handling. The first version may restrict itself to monomorphic definitions if needed.
- Declaration dependency ordering can be tricky when specializations refer to other generated specializations.
- Simplification can destroy sharing or unfold through matches in undesirable ways. The current transformer preserves sharing for nonlinear lambda beta-redexes, but broader let/match preservation still needs concrete tests.
- Proof construction is intentionally conservative; when a helper cannot construct a proof, generated declarations may still be useful but theorem generation can fail or be skipped.
- Lambda capture extraction changes generated arities for higher-order specializations. This is intentional, but dependent function arguments may need more careful treatment.
- Recursive definitions need cycle detection and should be skipped at first.
- Generated names must avoid collisions with user declarations and previous `#sas` runs.
