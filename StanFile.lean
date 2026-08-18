/-
lake exe stan_file — generate a standalone TFB file from a compiled project.

Usage (from the downstream project directory):
  lake exe stan_file <rootPrefix> <targetDecl> <outputPath>

Example:
  lake exe stan_file BridgelandStability \
    CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent \
    artifacts/trusted_base.lean
-/
import Stan

open Lean Stan.EmitStandalone Stan.Cli

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [root, target, output] =>
    let rootName := root.toName
    let targetName := target.toName
    let env ← loadProjectEnv rootName
    emitStandalone env rootName targetName output
  | _ =>
    IO.eprintln "Usage: lake exe stan_file <rootPrefix> <targetDecl> <outputPath>"
    IO.Process.exit 1
