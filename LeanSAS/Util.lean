import Lean

namespace LeanSAS

open Lean Meta

/--
Return the simp theorem set registered under `attr`.

The builtin `simp` attribute is handled specially because Lean exposes it through
`getSimpTheorems`; custom simp extensions are looked up in the environment.
-/
def getSimpTheoremsFor (attr : Name) : MetaM SimpTheorems := do
  if attr == `simp then
    getSimpTheorems
  else
    let some ext ← Lean.Meta.getSimpExtension? attr
      | throwError "simp attribute '{attr}' not found"
    ext.getTheorems

/--
Return the simproc set registered under `attr`.

This mirrors `getSimpTheoremsFor`: `simp` means the default global simprocs,
while other names are looked up as custom simproc extensions.
-/
def getSimprocsFor (attr : Name) : MetaM Simprocs := do
  if attr == `simp then
    Simp.getSimprocs
  else
    let some ext ← Simp.getSimprocExtension? attr
      | throwError "simproc attribute '{attr}' not found"
    ext.getSimprocs

/-- MetaM implementation of `withLocalDeclsD`. -/
private def withLocalDeclsDImpl {α}
    (decls : Array (Name × Expr)) (k : Array Expr → MetaM α) : MetaM α := do
  let rec go (i : Nat) (xs : Array Expr) : MetaM α := do
    if h : i < decls.size then
      let (n, t) := decls[i]
      withLocalDeclD n t fun x => go (i + 1) (xs.push x)
    else
      k xs
  go 0 #[]

/--
Introduce a sequence of default-binder local declarations.

`decls` contains the user-facing names and types. The continuation receives the
fresh free variables in the same order. The helper is lifted through monads that
support `MonadControlT MetaM`, which is needed because Lean local contexts live in
`MetaM` even when the caller is running in `SasM`.
-/
def withLocalDeclsD [Monad m] [MonadControlT MetaM m] {α}
    (decls : Array (Name × Expr)) (k : Array Expr → m α) : m α :=
  map1MetaM (withLocalDeclsDImpl decls) k

/--
Sanitize arbitrary text into a simple declaration-name component.

This is currently not used by the v1 name generator, which deliberately avoids
pretty-printed argument names, but it is useful for future diagnostic or
debug-oriented names.
-/
def sanitizeNamePart (s : String) : String :=
  let s := s.map fun c =>
    if c.isAlphanum || c == '_' then c else '_'
  if s.isEmpty then "spec" else s

end LeanSAS
