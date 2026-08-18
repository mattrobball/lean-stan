/-
Copyright (c) 2025 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard
-/
module

public meta import Lean

/-!
# CLI bootstrap helpers

Shared plumbing for `lake exe` entry points that need to load a downstream
project's compiled environment and then run `CoreM` actions against it.

Keeps the `initSearchPath` / `enableInitializersExecution` / `importModules`
dance in one place so individual exes stay tiny and the `loadExts := true`
invariant (see `loadProjectEnv`) is stated exactly once.
-/

public meta section

open Lean

namespace Stan.Cli

/-- Load a downstream project's compiled environment by its root module name.

    `loadExts := true` is critical: without it, parser extensions (custom
    notation like `+`, `⋙`, scoped syntax, etc.) are not loaded, causing
    `IO.processCommands` to produce truncated `Syntax` trees with wrong
    `getTailPos?` positions. The elab-command path picks extensions up
    automatically from `import`, but `importModules` defaults to
    `loadExts := false`, so exes have to opt in explicitly. -/
unsafe def loadProjectEnv (root : Name) : IO Environment := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  importModules (loadExts := true) #[{ module := root }] {} (trustLevel := 1024)

/-- Run a `CoreM` action against a loaded environment, discarding the final
    `Core.State`. Intended for exes that only need the action's result. -/
def runCoreM (env : Environment) (action : CoreM α) : IO α := do
  let ctx : Core.Context := { fileName := "<informal-cli>", fileMap := default }
  let state : Core.State := { env }
  Prod.fst <$> action.toIO ctx state

end Stan.Cli

end
