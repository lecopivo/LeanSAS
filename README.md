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

## How It Works

Given a function `f`, LeanSAS processes its body as follows:

1. Run `simp` on expressions during transformation.
2. Recursively inspect function applications in the body.
3. When a call `g x1 ... xn` is found, decide whether `g` can be specialized.
4. Arguments known at specialization time are baked into a generated specialization of `g`.
5. Arguments that still depend on runtime variables remain parameters of the generated specialization.
6. Replace the original call with a call to the generated specialization.
7. Repeat the process recursively for newly generated specializations.

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

## Simp Integration

LeanSAS is designed to use Lean's existing simplifier as the user extension mechanism.

The intended command syntax includes normal `simp` configuration and theorem selection:

```lean
#sas (config := {...}) only [thm1, thm2] f
```

The first implementation may start with the global `simp` set and add full syntax support after the core pass is working.

## First Version Scope

The first version will deliberately be small and conservative.

In scope:

- Generate `f._spec` for a Lean definition `f`.
- Recursively specialize non-recursive function calls.
- Bake compile-time-known arguments into generated definitions.
- Keep runtime-dependent arguments as parameters.
- Run `simp` during transformation.
- Generate real Lean declarations.

Out of scope for the first version:

- Recursive function specialization.
- Complex type encoding.
- Splitting one source argument into multiple generated arguments.
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

Simple examples the first version should support:

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
