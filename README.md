# lean-stan

Emit a **stan**dalone Lean file from a compiled project.

Given a target declaration, `lean-stan` walks everything that declaration's
*type* transitively depends on, and writes those project-local declarations
into a single file with proofs replaced by `sorry`. The result imports only
your external dependencies, compiles on its own, and is the statement surface
a reader has to trust in order to accept the target's statement.

Its intended use is as the challenge half of a
[Comparator](https://github.com/leanprover/comparator) check: the emitted file
states what you claim, your project proves it, and Comparator verifies the two
are the same statement.

## Install

```toml
[[require]]
name = "stan"
git = "https://github.com/mattrobball/lean-stan"
rev = "main"
```

No further dependencies -- `lean-stan` needs Lean core and nothing else, so it
builds in seconds and tracks whatever toolchain your project uses.

## Usage

```bash
lake exe stan_file <rootPrefix> <targetDecl> <outputPath>
```

Everything under `<rootPrefix>` is emitted; everything outside it is imported
and trusted as given. Build your project first -- `stan_file` reads the
compiled environment, not the sources alone.

```console
$ lake build MyProject
$ lake exe stan_file MyProject MyProject.Main.riemann_hyp_categorified_fake_true Challenge.lean
Target module: MyProject.Main
Imported modules: 6043
TFB: 57 declarations
Emitting from 12 modules
  MyProject/PostnikovTower/Defs.lean (2 decls)
  MyProject/Slicing/Defs.lean (7 decls)
  ...
Wrote Challenge.lean
```

The output reproduces your project's elaboration environment -- module header,
options, `open`s, `variable`s, per-module `universe` declarations -- then each
declaration in dependency order:

```lean
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
...

@[expose] public section
set_option backward.proofsInPublic true

-- ═══ PostnikovTower.Defs ═══

section
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MyProject
universe v u
variable (C : Type u) [Category.{v} C]

structure PostnikovTower (E : C) where
  ...

theorem someSupportingLemma (E : C) : P E := sorry
end
end
```

Note the `sorry`s: any declaration the skeleton leaves open must be listed in
Comparator's `theorem_names`, or Comparator will compare your real proof
against the skeleton's `sorryAx` and reject it.

### `stan_boundary`

```bash
lake exe stan_boundary --root <Pkg> [--root <Pkg> ...] \
  [--exclude <Prefix> ...] [--env <Module>] <targetDecl> <outputPath>
```

Use this instead of `stan_file` when your project spans several in-house
packages. `stan_file` takes a single root prefix and therefore imports any
other package of yours as if it were external; `stan_boundary` takes a set of
roots, inlines all of them, and leaves exactly your third-party dependencies
as the import surface. `--env` names the module to import to build the
environment, for when the target does not live under a root's own root module.

## Why the output is trustworthy

The emitted file has to *elaborate the way your project does*. If it does not,
it states something subtly different from what you proved, and it will do so
while compiling cleanly. Two rules keep that from happening:

**Commands are dropped by denylist, never kept by allowlist.** The emitter asks
one question per command -- does it declare something? -- drops non-target
declarations, and passes everything else through verbatim. An allowlist fails
open: an unrecognised command silently disappears. `set_option`, standalone
`omit`, `@[expose]` and the `module` header all change how declarations
elaborate or how they are recorded, and all four were being lost this way.

**Whether a command declares something is decided from the environment, not
from syntax kinds.** A command declares something iff some constant's
`declRange` lies within its span. Testing for `Parser.Command.declaration`
misses `lemma`, which is a macro; and the index must include internal names, or
`private` declarations go unrecognised.

`universe` commands are emitted per module rather than hoisted into one union,
because a declaration's `levelParams` follow the order of the enclosing
`universe` command and modules legitimately differ. Hoisting silently permutes
universe parameters -- invisible to any check comparing types modulo
universes, and fatal to Comparator, which compares exactly.

## License

Apache-2.0. See [LICENSE](LICENSE).
