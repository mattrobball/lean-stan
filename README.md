# lean-stan

Emit a **stan**dalone Lean file from a compiled project.

Given a target declaration, `lean-stan` collects everything that declaration
transitively depends on -- its type, and the bodies of any non-theorem
declarations that type reaches -- and writes those project-local declarations
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
rev = "v0.1.0"
```

Pin a tag or a commit rather than `main`: the whole point of the emitted file
is that regenerating it gives byte-identical output, and that only holds if the
generator is pinned too.

`lean-stan` has no dependencies beyond Lean core, so it adds nothing to your
build graph. Lake builds it with your project's toolchain, not the one in this
repository's `lean-toolchain` -- that file only fixes the version used when
developing `lean-stan` itself.

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
  MyProject/Widgets.lean (2 TFB decls)
  MyProject/Main.lean (1 TFB decls)
  ...
Wrote Challenge.lean
```

## What the output looks like

Every example below is invented -- names, modules and theorem alike. What is
faithful is the *shape*: the emitted file reproduces your project's elaboration
environment, because a skeleton that elaborates differently states something
different from what you proved.

The file opens with the module header, the external imports, and a generated
summary:

```lean
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Order.Basic

/-! # Trusted Formalization Base
MyProject — `MyProject.Main.riemann_hyp_categorified_fake_true`
Auto-generated — all proofs replaced with `sorry`.
57 declarations in dependency order.
-/
```

Then one block per source module. Each is wrapped in its own `section`, so its
options, `open`s, `universe` declarations and `variable`s cannot leak into the
next block:

```lean
-- ═══ Main ═══

section
@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.proofsInPublic true
noncomputable section
open Widgets
universe v u
namespace MyProject
variable (C : Type u) [Widgetable.{v} C]

theorem riemann_hyp_categorified_fake_true (E : C) : IsFake (widget C E) := sorry

end MyProject
end
end
end
```

Four `end`s close four openers: the wrapper `section`, the module's
`@[expose] public section`, its `noncomputable section`, and the `namespace`.

Note the `sorry`: any declaration the skeleton leaves open must be listed in
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

If the skeleton does not elaborate the way your project does, it states
something subtly different from what you proved -- and it does so while
compiling cleanly. Two rules keep that from happening:

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
