/-
Copyright (c) 2026 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard, Formalization
-/
module

public meta import Stan.EmitStandalone

/-!
# Boundary-aware standalone file generator

`EmitStandalone` draws its trust boundary with a single `rootPrefix`: modules
under it are inlined, everything else is imported and taken on faith. That is
the right boundary when a project is one package.

It is the wrong boundary when a project depends on another package that is
also ours. Then a single-prefix run silently imports in-house code as if it
were Mathlib, and the emitted file understates what a reader has to trust.

This module takes an `Array Name` of roots instead. A declaration is inlined
if it lives under ANY root, and imported otherwise. With every in-house
package named as a root, "imported" means exactly "external", which is the
boundary an audit actually wants.

The second difference is where source lives. `EmitStandalone` resolves a
module to `Foo/Bar.lean` relative to the working directory, which only holds
for the root project. Dependency packages sit under `.lake/packages/<pkg>/`,
so this module searches there too.

Everything else -- dependency collection, topological sort, InfoTree
re-elaboration, `sorry` injection, assembly -- is reused from
`EmitStandalone` unchanged.
-/

public meta section

open Lean Elab Command Meta Stan
open Stan.EmitStandalone

namespace Stan.EmitBoundary

/-- Is `mod` inside the trust boundary, i.e. under any of `roots`? -/
def inBoundary (roots : Array Name) (mod : Name) : Bool :=
  roots.any (·.isPrefixOf mod)

/-- The root that `mod` sits under, if any. Used to shorten section banners. -/
def matchingRoot? (roots : Array Name) (mod : Name) : Option Name :=
  roots.find? (·.isPrefixOf mod)

/-- Directories that could be a package root, to `depth` levels below `base`.

    A `require` with `subDir` clones the whole repository into
    `.lake/packages/<pkg>/` and the Lean package sits at `<subDir>` inside
    it, so the sources are not directly under the package directory. Rather
    than parse manifests for the subDir, look a couple of levels down. -/
partial def packageRoots (base : System.FilePath) (depth : Nat) : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[base]
  if depth == 0 then return out
  for entry in ← base.readDir do
    if (← entry.path.isDir) then
      -- `.lake` and `.git` hold build output and history, never sources.
      let name := entry.fileName
      unless name.startsWith "." do
        out := out ++ (← packageRoots entry.path (depth - 1))
  return out

/-- Candidate source paths for a module, in search order: the root project
    first, then each package under `.lake/packages/` and its plausible
    subdirectory roots. -/
def sourceCandidates (modName : Name) : IO (Array System.FilePath) := do
  let rel := System.FilePath.mk (modName.toString.replace "." "/" ++ ".lean")
  let mut out : Array System.FilePath := #[rel]
  let pkgRoot : System.FilePath := ".lake/packages"
  if ← pkgRoot.pathExists then
    for entry in ← pkgRoot.readDir do
      if (← entry.path.isDir) then
        for root in ← packageRoots entry.path 2 do
          out := out.push (root / rel)
  return out

/-- Locate a module's source file. Returns `none` if nothing matches, which
    the caller reports rather than crashing -- a module whose source is not on
    disk cannot be inlined, and silently dropping it would understate the
    boundary. -/
def resolveSource (modName : Name) : IO (Option System.FilePath) := do
  for cand in ← sourceCandidates modName do
    if ← cand.pathExists then
      return some cand
  return none

/-- Names to inline: the target plus every dependency living under a root.

    Mirrors `EmitStandalone.computeTFBNames`, differing only in testing
    membership against an array of roots rather than one prefix. -/
def computeBoundaryNames (env : Environment) (roots : Array Name) (targetName : Name)
    (excludePrefixes : Array Name := #[])
    (importedEnv? : Option Environment := none) : Except String (Std.HashSet Name) := do
  let some ci := env.find? targetName
    | .error s!"Target declaration '{targetName}' not found in environment"
  let keep (resolved : Name) (isPriv : Bool) : Bool :=
    match env.getModuleIdxFor? resolved with
    | some idx =>
      let modName := env.header.moduleNames[idx.toNat]!
      inBoundary roots modName
        && !excludePrefixes.any (·.isPrefixOf modName)
        && (isPriv || (classifyNonUser env resolved).isNone)
    | none => false
  let skipImported (resolved : Name) : Bool :=
    match importedEnv? with
    | some impEnv => impEnv.contains resolved
    | none => false
  let rawDeps := collectDeps env targetName ci (proofIrrelevant := true) (roots := roots)
  let mut result : Std.HashSet Name := {}
  result := result.insert targetName
  -- Parents that entered the set only by promotion, so were never walked.
  let mut promoted : Array Name := #[]
  for dep in rawDeps.toArray do
    -- Private declarations keep their INTERNAL name: `classifyNonUser` calls
    -- anything `_`-prefixed internal, right for compiler artifacts and wrong
    -- for `private abbrev k`, a real declaration the emitted source names.
    -- Dropping it leaves `k` unbound, autoImplicit invents a variable, and
    -- the failure surfaces as `Semiring k` rather than a missing identifier.
    let isPriv := isPrivateName dep
    let resolved := if isPriv then dep else resolveToUser env dep
    if skipImported resolved then continue
    if keep resolved isPriv then
      result := result.insert resolved
      -- `resolveToUser` promotes an auxiliary to its parent, so a declaration
      -- can be emitted that the walk never visited: only
      -- `instFintypeCircle1._proof_1` is reached, it resolves to
      -- `instFintypeCircle1`, and the instance is emitted while `Circle1`,
      -- which its type names, was never collected. Promotion adds a
      -- declaration to the output, so its dependencies have to come too.
      if resolved != dep && !rawDeps.contains resolved then
        promoted := promoted.push resolved
  -- One extra walk per promoted parent -- a handful, not per closure member.
  for p in promoted do
    if let some pci := env.find? p then
      for dep in (collectDeps env p pci (proofIrrelevant := true) (roots := roots)).toArray do
        let isPriv := isPrivateName dep
        let resolved := if isPriv then dep else resolveToUser env dep
        if !skipImported resolved && keep resolved isPriv then
          result := result.insert resolved
  if let some impEnv := importedEnv? then
    if impEnv.contains targetName then
      result := result.erase targetName
  return result

/-- Emit a standalone file whose trust boundary is `roots`.

    Declarations under any root are inlined with proofs replaced by `sorry`;
    everything else is imported. Name every in-house package as a root and the
    result imports only genuinely external code. -/
def emitBoundary (env : Environment) (roots : Array Name) (targetName : Name)
    (outputPath : System.FilePath)
    (excludePrefixes : Array Name := #[]) : IO Unit := do
  if roots.isEmpty then
    throw (IO.userError "emitBoundary: at least one --root is required")

  let targetModName := match env.getModuleIdxFor? targetName with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => roots[0]!
  IO.eprintln s!"Target module: {targetModName}"
  IO.eprintln s!"Boundary roots: {roots}"

  let names ← match computeBoundaryNames env roots targetName excludePrefixes with
    | .ok names => pure names
    | .error msg => throw (IO.userError msg)
  IO.eprintln s!"Inside boundary: {names.size} declarations"

  -- Module order follows env.header.moduleNames, which importModulesCore
  -- builds dependency-first, so it is already a valid topological order.
  let mut moduleSet : Std.HashSet Name := {}
  for name in names do
    if let some idx := env.getModuleIdxFor? name then
      moduleSet := moduleSet.insert env.header.moduleNames[idx.toNat]!
  let mut modIdxPairs : Array (Name × Nat) := #[]
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if moduleSet.contains modName then
      modIdxPairs := modIdxPairs.push (modName, i)
  let orderedModules := (modIdxPairs.qsort fun a b => a.2 < b.2).map (·.1)
  IO.eprintln s!"Emitting from {orderedModules.size} modules"

  -- Per-module extraction, reusing EmitStandalone.processFile.
  let mut allModules : Array ModuleContent := #[]
  let mut unresolved : Array Name := #[]
  for modName in orderedModules do
    let some filePath ← resolveSource modName
      | unresolved := unresolved.push modName
        IO.eprintln s!"  !! {modName}: source not found, SKIPPED"
        continue
    let source ← IO.FS.readFile filePath
    let fileMap := FileMap.ofString source
    let mut rangeMap : Std.HashMap String.Pos.Raw Name := {}
    for name in names do
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]! == modName then
          if let some ranges := findDeclRanges? env name then
            rangeMap := rangeMap.insert (fileMap.ofPosition ranges.range.pos) name
    -- Every declaration in this module, so `processFile` can tell a declaration
    -- command from a context command without guessing at syntax kinds.
    let mut declPositions : Array String.Pos.Raw := #[]
    for (n, _) in env.constants.toList do
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! == modName then
          if let some ranges := findDeclRanges? env n then
            declPositions := declPositions.push (fileMap.ofPosition ranges.range.pos)
    IO.eprintln s!"  {filePath} ({rangeMap.size} decls)"
    let entries ← processFile source env rangeMap declPositions filePath.toString
    allModules := allModules.push { modName, entries := stripEmptySections entries }

  -- Mathlib wholesale, then every non-Mathlib external import by name.
  --
  -- Naming the individual Mathlib modules used is not worth the risk: the
  -- imports have to be harvested from somewhere, and harvesting from the
  -- modules that contributed declarations misses any module that contributes
  -- none yet is the sole route by which an import arrives.
  -- V14Formalization.Basic is exactly that -- Definitions uses
  -- `Representation` without importing it, getting it via Basic -- and the
  -- emitted file then fails to elaborate. Mathlib is trusted as given
  -- either way, so importing all of it costs only load time.
  --
  -- Non-Mathlib externals still have to be named, and for those the source
  -- is every in-boundary module in the environment, not just the ones that
  -- contributed declarations, for the same completeness reason.
  let mut output := "import Mathlib\n"
  let mut emitted : Std.HashSet Name := {}
  let mut importSources : Array Name := #[]
  for modName in env.header.moduleNames do
    if inBoundary roots modName then
      importSources := importSources.push modName
  importSources := importSources.push targetModName
  for modName in importSources do
    match env.getModuleIdx? modName with
    | some idx =>
      for imp in env.header.moduleData[idx.toNat]!.imports.map Import.module do
        if imp != `Init && !inBoundary roots imp
            && imp.getRoot != `Mathlib
            && !((`Informal).isPrefixOf imp) && !((`Stan).isPrefixOf imp)
            && !((`ProblemExtraction).isPrefixOf imp)
            && !emitted.contains imp then
          emitted := emitted.insert imp
          output := output ++ s!"import {imp}\n"
    | none => pure ()
  output := output ++ "\n"

  let mut universeNames : Array String := #[]
  for mc in allModules do
    for e in mc.entries do
      if e.cls == .context && e.kind == ``Parser.Command.universe then
        for word in e.src.splitOn " " do
          let w := word.trimAsciiEnd.toString
          if w != "universe" && !w.isEmpty && !universeNames.contains w then
            universeNames := universeNames.push w

  output := output ++ "/-! # Trusted base\n\n"
  output := output ++ s!"Target: `{targetName}`\n\n"
  output := output ++ s!"Boundary: {", ".intercalate (roots.toList.map toString)}\n\n"
  output := output ++ s!"{names.size} declarations from {orderedModules.size} modules, \
    inlined in dependency order with every proof replaced by `sorry`. Imports above \
    are outside the boundary and are trusted as given.\n"
  unless unresolved.isEmpty do
    output := output ++ s!"\nWARNING: source not found for \
      {", ".intercalate (unresolved.toList.map toString)} -- \
      these are INSIDE the boundary but could not be inlined.\n"
  output := output ++ "-/\n\n"
  unless universeNames.isEmpty do
    output := output ++ "universe " ++ " ".intercalate universeNames.toList ++ "\n\n"

  for mc in allModules do
    let hasDecl := mc.entries.any fun e => match e.cls with | .tfbDecl _ => true | _ => false
    if !hasDecl then continue
    let shortName := match matchingRoot? roots mc.modName with
      | some r => mc.modName.toString.drop (r.toString.length + 1)
      | none => mc.modName.toString
    output := output ++ s!"-- ═══ {shortName} ═══\n\n"
    let mut prevWasDecl := false
    for e in mc.entries do
      match e.cls with
      | .context =>
        if e.kind == ``Parser.Command.universe then continue
        if e.kind == ``Parser.Command.set_option then continue
        -- `open N` where N is inside the boundary but contributed no
        -- declaration names a namespace that does not exist in the emitted
        -- file, which Lean rejects outright. External opens are always kept:
        -- their namespaces come in via the imports.
        -- Same reasoning for `attribute [...] N`: if N is inside the
        -- boundary but was not emitted, the command names something the file
        -- does not contain. Re-enabling `attribute` as context is what made
        -- `attribute [instance] SmoothProjectiveGVariety.ambientAdd` appear
        -- for a structure that is not in the closure.
        if e.kind == ``Parser.Command.attribute then
          let after := (e.src.splitOn "]").getLast!
          let toks := (after.splitOn " ").filterMap fun t =>
            let t := t.trim
            if t.isEmpty then none else some t
          -- Source writes these relative to the enclosing namespace
          -- (`SmoothProjectiveGVariety.ambientAdd`) while the closure holds
          -- them absolute (`V14Formalization.SmoothProjectiveGVariety...`),
          -- so resolve against each root before deciding. A token that does
          -- not resolve in-boundary is external -- e.g.
          -- `MvPolynomial.gradedAlgebra` -- and must be kept.
          let dead := toks.any fun t => Id.run do
            let tn := t.toName
            for r in roots do
              let cand := r ++ tn
              if env.contains cand then
                return !names.contains cand
            return false
          if dead then continue
        if e.kind == ``Parser.Command.open then
          let toks := (e.src.splitOn " ").filterMap fun t =>
            let t := t.trim
            if t.isEmpty || t == "open" then none else some t
          let dead := toks.any fun t =>
            let n := t.toName
            inBoundary roots n && !names.toArray.any (fun d => n.isPrefixOf d)
          if dead then continue
        if prevWasDecl then output := output ++ "\n"
        output := output ++ e.src ++ "\n"
        prevWasDecl := false
      | .tfbDecl _ =>
        output := output ++ "\n"
        output := output ++ e.src ++ "\n"
        prevWasDecl := true
      | .skip => pure ()
    output := output ++ "\n"

  -- These attributes would require importing Informal, which the emitted file
  -- does not do.
  let filtered := output.splitOn "\n" |>.filter fun line =>
    let t := line.trimAsciiStart.toString
    !(t.startsWith "@[informal " || t.startsWith "@[expose]")
  output := ("\n".intercalate filtered).trimAsciiEnd.toString ++ "\n"

  IO.FS.writeFile outputPath output
  IO.eprintln s!"Wrote {outputPath}"
  unless unresolved.isEmpty do
    IO.eprintln s!"WARNING: {unresolved.size} in-boundary module(s) had no source on disk"

end Stan.EmitBoundary

end
