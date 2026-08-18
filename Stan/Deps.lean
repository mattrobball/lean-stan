/-
Copyright (c) 2025 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard
-/
module

public meta import Lean

/-!
# Transitive dependency collection

Computes the transitive closure of project-local constants referenced by a
declaration. Returns a raw `NameSet` — no resolution, no hashing.

The `proofIrrelevant` flag controls whether theorem values are followed:
- `true`: skip theorem bodies (only follow their types)
- `false`: follow everything (for axiom-style audits)
-/

public meta section

open Lean

namespace Stan

/-- Is this a proof auxiliary that elaboration lifted out of a definition?

    A proof term is abstracted into its own constant as soon as it contains a
    nested proof argument: `exB (exA n)` becomes `foo._proof_1`, while the
    atomic `exA n` stays inline. Identical on v4.29.1, v4.31.0 and v4.32.1. -/
def isLiftedProof : Name → Bool
  | .str _ s => s.startsWith "_proof"
  | _ => false

/-- One-level used constants for a `ConstantInfo`.
When `proofIrrelevant` is true, skips theorem values -- EXCEPT for lifted
proof auxiliaries, whose values are always followed.

A user theorem's proof can be skipped: the emitter replaces it with `sorry`.
A lifted auxiliary cannot. It is a fragment of a definition whose source is
emitted verbatim, and that source names the constants it was abstracted
from, so skipping its value drops names the emitted file still references.
Restricted to `_proof` by name rather than to every auxiliary: Mathlib is
full of constants that resolve to a parent, and following all of them walks
its entire proof DAG.

Exhaustive on all `ConstantInfo` constructors. -/
def usedConstants (ci : ConstantInfo) (proofIrrelevant : Bool := true) : NameSet :=
  ci.type.getUsedConstantsAsSet ++ match ci with
  | .thmInfo v    =>
      if proofIrrelevant && !isLiftedProof ci.name then {} else v.value.getUsedConstantsAsSet
  | .defnInfo v   => v.value.getUsedConstantsAsSet
  | .opaqueInfo v => v.value.getUsedConstantsAsSet
  | .inductInfo v => .ofList v.ctors
  | .ctorInfo v   => ({} : NameSet).insert v.name
  | .recInfo v    => .ofList v.all
  | .axiomInfo _  => {}
  | .quotInfo _   => {}

private structure CollectState where
  visited : NameSet := {}
  deps : NameSet := {}

private abbrev CollectM := ReaderT (Environment × Array Name × Bool) (StateM CollectState)

/-- Recursively collect the transitive closure of dependencies.
Records every project-local constant encountered — no filtering,
no derivative resolution. -/
private partial def collect (c : Name) : CollectM Unit := do
  let s ← get
  if s.visited.contains c then return
  modify fun s => { s with visited := s.visited.insert c }
  let (env, roots, pi) ← read
  let some ci := env.find? c | return
  match env.getModuleIdxFor? c with
  | some idx =>
    if roots.any (·.isPrefixOf env.header.moduleNames[idx.toNat]!) then
      modify fun s => { s with deps := s.deps.insert c }
  | none => pure ()
  (usedConstants ci pi).forM collect

/-- Compute the transitive closure of dependencies for a declaration.
Returns every constant in the dependency graph that lives under one of
`roots`.

When `proofIrrelevant` is true (default), theorem values are skipped
but their types are still followed.

`roots` defaults to the root of the module holding `name`, which is right
when the declaration and its dependencies belong to one package. It is wrong
whenever they do not -- a challenge module stating a theorem about
definitions from elsewhere, or a project spanning several in-house packages.
In those cases every dependency has a different module root than the target
and the closure silently comes back holding only the target itself, so pass
the roots explicitly. -/
def collectDeps (env : Environment) (name : Name) (ci : ConstantInfo)
    (proofIrrelevant : Bool := true) (roots : Array Name := #[]) : NameSet := Id.run do
  let roots := if roots.isEmpty then
      #[match env.getModuleIdxFor? name with
        | some idx => env.header.moduleNames[idx.toNat]!.getRoot
        | none => env.mainModule.getRoot]
    else roots
  let mut s : CollectState := {}
  s := { s with visited := s.visited.insert name }
  (_, s) := ((usedConstants ci proofIrrelevant).forM collect
    |>.run (env, roots, proofIrrelevant)).run s
  s.deps

end Stan

end
