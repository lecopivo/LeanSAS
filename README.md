# LeanSAS

LeanSAS is a Lean library for experimenting with a specialization and simplification compilation pre-pass.

The core idea is to take a Lean definition, generate a specialized version of it, recursively specialize the functions it calls, and run `simp` on generated bodies. Users can then guide the generated code by providing ordinary `simp` theorems and simprocs.

## Motivation

Lean functions are often written in a generic, reusable style. That style is good for proofs and source code, but it can leave generated code with unnecessary abstraction:

- calls where some arguments are statically known,
- helper functions that could be specialized to concrete arguments,
- generic definitions that simplify substantially after specialization,
- terms that become computationally useful only after user-provided `simp` rules fire.

LeanSAS aims to provide a small pre-pass that turns such definitions into simpler specialized definitions before later compilation or extraction steps.

## Command

The intended command is:

```lean
#sas f
```

For a definition `f`, this command creates a generated definition named:

```lean
f._spec
```

The generated definition is extensionally the same computation as `f`, but its body is transformed by the specialization pass.

For each generated specialization, LeanSAS also tries to add an equality theorem:

```lean
f._spec.eq_thm
```

The theorem states that the generated specialization computes the same value as the original declaration at each runtime argument.

## How It Works

Given a function `f`, LeanSAS processes its body as follows:

1. Run `simp` on expressions during transformation.
2. Recursively inspect function applications in the body.
3. When a call `g x1 ... xn` is found, decide whether `g` can be specialized.
4. Arguments known at specialization time are baked into a generated specialization of `g`.
5. Arguments that still depend on runtime variables remain parameters of the generated specialization.
6. Lambda arguments are treated as static templates; their captured free variables become deduplicated runtime parameters of the specialization.
7. Replace the original call with a call to the generated specialization.
8. Repeat the process recursively for newly generated specializations.

For example, a source call like this:

```lean
scaleAdd 2 x
```

may produce a generated specialization equivalent to:

```lean
def scaleAdd._spec_1 (x : Nat) :=
  scaleAdd 2 x
```

and the original call site is rewritten to:

```lean
scaleAdd._spec_1 x
```

The body of `scaleAdd._spec_1` is then processed by the same specialization and simplification pass.

Higher-order arguments are specialized too. For example:

```lean
def functionArgCallee (f : Nat → Nat) (x : Nat) :=
  f x

def functionArgTransform (x z : Nat) :=
  functionArgCallee (fun y => 0 + y*z + x) x
```

may generate a callee specialization shaped like:

```lean
def functionArgCallee_sas_1 (x z : Nat) :=
  x * z + x
```

The lambda itself is baked into the specialization, while the captured variables `x` and `z` become generated parameters. Captures are deduplicated against ordinary runtime arguments.

When a specialized lambda uses its parameter nonlinearly, LeanSAS preserves sharing for nontrivial arguments by introducing a `let` before beta reduction. For example, specializing `f (expensive x)` with `fun y => a*y + b*y` produces a body shaped like:

```lean
let y := expensive._spec x
a * y + b * y
```

instead of duplicating `expensive._spec x`.

## Simp Integration

LeanSAS is designed to use Lean's existing simplifier as the user extension mechanism.

The intended command syntax includes normal `simp` configuration and theorem selection:

```lean
#sas (config := {...}) only [thm1, thm2] f
```

The command supports ordinary `simp` attribute selection and configuration, including `only [...]`, added theorem sets, removed theorem sets, and `(config := ...)`.

## Current Scope

The current version is deliberately small and conservative, but it already supports the core specialization pass.

In scope:

- Generate `f._spec` for a Lean definition `f`.
- Recursively specialize non-recursive function calls.
- Bake compile-time-known arguments into generated definitions.
- Keep runtime-dependent arguments as parameters.
- Run `simp` during transformation.
- Generate real Lean declarations.
- Generate equality theorems for generated specializations when proof construction succeeds.
- Compose proof terms across simplification, application argument rewriting, lambda congruence, let congruence, and projection congruence.
- Specialize lambda-valued arguments by extracting captured runtime variables.
- Preserve sharing for nonlinear beta-redexes with nontrivial arguments.

Still out of scope:

- Recursive function specialization.
- Complex type encoding.
- General splitting of source arguments into multiple generated arguments, except for lambda captures used by higher-order specialization.
- OpenCL-specific behavior.
- Primitive interpreter evaluation.
- Direct compiler-pipeline integration.

## Type Encoding Direction

Type encoding is not part of the first version.

When type encoding is added later, LeanSAS should use a simple one-type-to-one-type model. A source type may be encoded into another type, but it should remain one argument slot.

For example:

```lean
Option A  ~~>  A × Bool
```

not:

```lean
Option A  ~~>  A, Bool
```

This differs from the previous prototype, which tried to flatten structure-like values into multiple arguments in some cases. The simpler model keeps generated function arities more predictable and should make the pass easier to maintain.

## Example Targets

Simple examples supported by the current implementation:

```lean
def addOne (x : Nat) := x + 1
def useAddOne (n : Nat) := addOne n

#sas useAddOne
#check useAddOne._spec
```

```lean
def scaleAdd (k x : Nat) := k * x + 1
def byTwo (x : Nat) := scaleAdd 2 x

#sas byTwo
#check byTwo._spec
```

```lean
def f (a b : Nat) := a + b
def g (x : Nat) := f 10 x
def h (x : Nat) := g (x + 1)

#sas h
#check h._spec
```

Higher-order lambda specialization:

```lean
def functionArgCallee (f : Nat → Nat) (x : Nat) :=
  f x

def functionArgTransform (x z : Nat) :=
  functionArgCallee (fun y => 0 + y*z + x) x

#sas functionArgTransform
#print functionArgTransform._spec
#print functionArgCallee_sas_1
```

Sharing-preserving nonlinear beta specialization:

```lean
def expensiveInput (x : Nat) := x + 1

def nonlinearFunctionArgCallee (f : Nat → Nat) (x : Nat) :=
  f (expensiveInput x)

def nonlinearFunctionArgTransform (a b x : Nat) :=
  nonlinearFunctionArgCallee (fun y => a * y + b * y) x

#sas (config := { zeta := false }) nonlinearFunctionArgTransform
#print nonlinearFunctionArgCallee_sas_1
```

## Previous Attempt

The previous and more ambitious prototype is located at:

```text
~/Documents/HouLean/HouLean/Meta/SpecializeAndSimp2/
```

Partially broken tests and examples are located at:

```text
~/Documents/HouLean/Tests/Meta/SpecAndSimp/
```

That implementation contains useful ideas, especially the recursive specialization request queue, but it also includes complex type encoding, vector/matrix-specific machinery, primitive evaluation hooks, and HouLean-specific dependencies. LeanSAS should first extract the small core and build from there.

## Development Plan

See [`PLAN.md`](PLAN.md) for the implementation plan and milestone list.
