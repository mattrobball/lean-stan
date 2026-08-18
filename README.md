# lean-stan

Generates a **stan**dalone Lean file from a compiled project: given a target
declaration, it emits every project-local declaration that target's *type*
transitively depends on -- the trusted formalization base -- into a single
file whose import closure is external dependencies only, with proofs replaced
by `sorry`.

The result is the statement surface a reader has to trust in order to accept
the target's statement, in a form that compiles on its own and can be checked
against the original by a tool such as
[Comparator](https://github.com/leanprover/comparator).

## Executables

```bash
# one root prefix; anything outside it is imported and trusted as given
lake exe stan_file <rootPrefix> <targetDecl> <outputPath>

# several package roots; everything else becomes the import surface
lake exe stan_boundary --root <Pkg> [--root <Pkg> ...] \
  [--exclude <Prefix> ...] [--env <Module>] <targetDecl> <outputPath>
```

## Fidelity

The emitted file has to elaborate the way the project does, or the skeleton
states something subtly different from what was proved. Two design rules
follow, and both are load-bearing:

* **Commands are dropped by denylist, never kept by allowlist.** The emitter
  asks one question per command -- does it declare something? -- drops
  non-target declarations, and passes everything else through verbatim. An
  allowlist fails open: an unrecognised command vanishes and the result still
  compiles while meaning something else. `set_option`, standalone `omit`,
  `@[expose]` and the `module` header all change how declarations elaborate or
  are recorded.

* **That question is answered from the environment, not from syntax kinds.** A
  command declares something iff some constant's `declRange` lies within its
  span. Checking for `Parser.Command.declaration` misses `lemma`, which is a
  macro, and the index must include internal names or `private` declarations go
  unrecognised.

`universe` commands are emitted per module rather than hoisted into one union,
because a declaration's `levelParams` follow the order of the enclosing
`universe` command and modules legitimately differ.

## Dependencies

None beyond Lean core -- that is the point. See `lakefile.toml`.
