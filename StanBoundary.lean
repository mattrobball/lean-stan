/-
lake exe stan_boundary — generate a standalone file whose trust boundary is a
set of package roots rather than a single prefix.

Usage (from the downstream project directory):
  lake exe stan_boundary --root <Pkg> [--root <Pkg> ...]
    [--exclude <Prefix> ...] [--env <Module>] <targetDecl> <outputPath>

Declarations under any `--root` are inlined with proofs replaced by `sorry`.
Everything else is imported and trusted as given. Name every in-house package
as a root and the emitted file's imports are exactly the external surface.

`--env` names the module to import to build the environment. It defaults to
the root that the target sits under, which is right when the target lives in
the package's root module. It is NOT right when the target lives in a module
the root does not import -- a separate challenge or solution library, say --
so pass that module explicitly.

Example:
  lake exe stan_boundary \
    --root V14Formalization \
    --root BConicBundleMultisections \
    --env V14Solution \
    V14Formalization.Comparator.noEquivariantRationalMap_from_ambient \
    artifacts/trusted_base.lean

Compare `stan_file`, which takes one root prefix and so imports any other
in-house package as if it were external.
-/
import Stan

open Lean Stan.EmitBoundary Stan.Cli

structure Args where
  roots : Array Name := #[]
  excludes : Array Name := #[]
  env? : Option Name := none
  target : Option Name := none
  output : Option System.FilePath := none

partial def parseArgs : List String → Args → Except String Args
  | [], acc => .ok acc
  | "--root" :: v :: rest, acc =>
      parseArgs rest { acc with roots := acc.roots.push v.toName }
  | "--exclude" :: v :: rest, acc =>
      parseArgs rest { acc with excludes := acc.excludes.push v.toName }
  | "--env" :: v :: rest, acc =>
      parseArgs rest { acc with env? := some v.toName }
  | v :: rest, acc =>
      -- Flags are matched with their values above, so reaching here with a
      -- leading `--` means either a known flag missing its value (nothing
      -- left to consume) or an unknown one. Positionals must stay in this
      -- branch: an earlier `_ :: []` case would swallow the output path.
      if v.startsWith "--" then
        if rest.isEmpty then .error s!"flag '{v}' given without a value"
        else .error s!"unknown flag '{v}'"
      else if acc.target.isNone then parseArgs rest { acc with target := some v.toName }
      else if acc.output.isNone then parseArgs rest { acc with output := some v }
      else .error s!"unexpected extra argument '{v}'"

def usage : String :=
  "Usage: lake exe stan_boundary --root <Pkg> [--root <Pkg> ...] \
   [--exclude <Prefix> ...] [--env <Module>] <targetDecl> <outputPath>"

unsafe def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error msg =>
    IO.eprintln s!"error: {msg}"
    IO.eprintln usage
    return 1
  | .ok a =>
    if a.roots.isEmpty then
      IO.eprintln "error: at least one --root is required"
      IO.eprintln usage
      return 1
    let some target := a.target
      | IO.eprintln "error: no target declaration given"
        IO.eprintln usage
        return 1
    let some output := a.output
      | IO.eprintln "error: no output path given"
        IO.eprintln usage
        return 1
    let envRoot := match a.env? with
      | some m => m
      | none => (a.roots.find? (·.isPrefixOf target)).getD a.roots[0]!
    IO.eprintln s!"Loading environment from: {envRoot}"
    let env ← loadProjectEnv envRoot
    emitBoundary env a.roots target output a.excludes
    return 0
