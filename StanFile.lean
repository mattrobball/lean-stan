/-
lake exe stan_file — generate a standalone TFB file from a compiled project.

Usage (from the downstream project directory):
  lake exe stan_file [--verify] <rootPrefix> <targetDecl> <outputPath>

Example:
  lake exe stan_file --verify BridgelandStability \
    CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent \
    artifacts/trusted_base.lean

`--verify` re-elaborates the file just written, in a fresh environment built
from that file's own imports, and compares every declaration it produces
against the project. Exits non-zero on any mismatch.

It is a flag rather than the default because it costs a second elaboration of
the emitted file's whole import closure -- for a Mathlib-scale project that is
real time and memory. CI should pass it; an author iterating locally need not.
-/
import Stan
import Stan.Verify

open Lean Stan.EmitStandalone Stan.Cli

unsafe def run (verify : Bool) (root target output : String) : IO Unit := do
  let rootName := root.toName
  let targetName := target.toName
  let env ← loadProjectEnv rootName
  emitStandalone env rootName targetName output
  if verify then
    unless (← Stan.Verify.verifyEmitted env output) do
      IO.Process.exit 1

unsafe def main (args : List String) : IO Unit := do
  match args with
  | ["--verify", root, target, output] => run true root target output
  | [root, target, output] => run false root target output
  | _ =>
    IO.eprintln "Usage: lake exe stan_file [--verify] <rootPrefix> <targetDecl> <outputPath>"
    IO.Process.exit 1
