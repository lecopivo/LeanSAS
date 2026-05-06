# LeanSAS Implementation Plan

This plan describes the first implementation of LeanSAS: a Lean specialization and simplification pre-pass exposed through the `#sas` command.

The first version intentionally avoids the previous attempt's complex type encoding system. The goal is to get a small, reliable core working first: specialize functions by baking compile-time-known arguments into generated definitions, recursively specialize callees, and simplify generated bodies with `simp`.

## Goals

- Provide a command `#sas f` that creates a generated definition `f._spec`.
- Run `simp` on generated bodies during specialization.
- Recursively specialize non-recursive callees used by `f`.
- Bake arguments known at specialization time into generated definitions.
- Keep runtime arguments as parameters of the generated specialization.
- Generate real Lean declarations, not only log messages.
- Keep the implementation independent of HouLean-specific libraries.

## Non-Goals For The First Version

- Do not implement structure/vector/matrix flattening.
- Do not split one source argument into several generated arguments.
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
  - Register trace classes such as `LeanSAS.sas` and `LeanSAS.sas.simp`.

- `LeanSAS/Util.lean`
  - Helper functions for simp extensions and expression utilities.
  - Minimal match/let preservation helpers if needed.

- `LeanSAS/Types.lean`
  - `SpecializationRequest`
  - `Specialization`
  - `Context`
  - `State`
  - `SasM := ReaderT Context <| StateT State <| SimpM`
  - `SasM.run`

- `LeanSAS/Main.lean`
  - Core expression transformer.
  - Function call specialization.
  - Specialization request queue.
  - Public `sas` entry point.

- `LeanSAS/Command.lean`
  - The `#sas` command.
  - Later support for explicit simp configuration syntax.

- `Tests/Basic.lean`
  - Small examples and `#guard_msgs` tests.

The root `LeanSAS.lean` should import the command module once the implementation exists.

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
   - Build a generated specialization of `g` over only the remaining runtime arguments.
   - Replace the original call with a call to the generated specialization.
   - Queue the generated specialization for processing.
6. Process specialization requests until the queue is empty.
7. Add all generated declarations to the environment.

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
g._spec_1
g._spec_2
```

Avoid relying on pretty-printed argument values for names in the first version. Pretty-printed names are useful for debugging but fragile as declaration names.

## Simp Support

The first version should run `simp` with a conservative configuration:

```lean
{ zeta := false, zetaDelta := false, iota := true }
```

Initial command support can use the global `simp` set. Support for full command syntax can be added after the core pass works:

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

## Milestones

1. Port the minimal monad and simp runner.
2. Implement the recursive expression traversal.
3. Implement call-site specialization and request queueing.
4. Implement declaration generation for generated specializations.
5. Implement `#sas f` for monomorphic non-recursive definitions.
6. Add the basic tests above.
7. Improve robustness for let-bindings, projections, matches, and name collisions.
8. Add explicit simp theorem/config syntax.
9. Design and implement the later one-type-to-one-type encoding layer.

## Known Risks

- Universe-polymorphic definitions require careful level parameter handling. The first version may restrict itself to monomorphic definitions if needed.
- Declaration dependency ordering can be tricky when specializations refer to other generated specializations.
- Simplification can destroy sharing or unfold through matches in undesirable ways. Use `zeta := false` and add let/match preservation only when a concrete test requires it.
- Recursive definitions need cycle detection and should be skipped at first.
- Generated names must avoid collisions with user declarations and previous `#sas` runs.
