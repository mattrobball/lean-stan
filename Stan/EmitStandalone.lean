/-
Copyright (c) 2025 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard, Formalization
-/
module

public meta import Stan.Deps
public meta import Stan.Classify
public meta import Lean

/-!
# Standalone TFB file generator

Given a compiled Lean environment and a target declaration name, generates a
single standalone `.lean` file containing all transitive type-level dependencies
(the Trusted Formalization Base) with proofs replaced by `sorry`.

Uses InfoTree re-elaboration (reusing the project env) to get per-command
Syntax. Matches commands to TFB declarations via DeclarationRanges byte
positions. Surgical `declVal` replacement for sorry injection.

Each command is classified by its Syntax kind and carried as a structured
`CommandEntry` through to the assembly phase — no string re-parsing needed.
-/

public meta section

open Lean Elab Command Meta Stan

namespace Stan.EmitStandalone

-- ═══ Phase 1: TFB name computation ═══

def computeTFBNames (env : Environment) (rootPrefix : Name) (targetName : Name)
    (excludePrefixes : Array Name := #[])
    (importedEnv? : Option Environment := none) : Except String (Std.HashSet Name) := do
  let some ci := env.find? targetName
    | .error s!"Target declaration '{targetName}' not found in environment"
  let rawDeps := collectDeps env targetName ci (proofIrrelevant := true)
  let mut result : Std.HashSet Name := {}
  result := result.insert targetName
  for dep in rawDeps.toArray do
    let resolved := resolveToUser env dep
    -- Skip declarations already available from the import
    if let some impEnv := importedEnv? then
      if impEnv.contains resolved then continue
    match env.getModuleIdxFor? resolved with
    | some idx =>
      let modName := env.header.moduleNames[idx.toNat]!
      if rootPrefix.isPrefixOf modName
          && !excludePrefixes.any (·.isPrefixOf modName)
          && (classifyNonUser env resolved).isNone then
        result := result.insert resolved
    | none => pure ()
  -- Also check if target itself is already imported
  if let some impEnv := importedEnv? then
    if impEnv.contains targetName then
      result := result.erase targetName
  return result

-- ═══ Phase 2: Topological sort (Kahn's algorithm) ═══

def directDepsInSet (env : Environment) (name : Name) (relevantNames : Std.HashSet Name)
    : Array Name := Id.run do
  let some ci := env.find? name | return #[]
  let used := usedConstants ci (proofIrrelevant := true)
  let mut deps : Array Name := #[]
  for u in used.toArray do
    let resolved := resolveToUser env u
    if relevantNames.contains resolved && resolved != name then
      deps := deps.push resolved
  deps.toList.eraseDups.toArray

def topologicalSort (env : Environment) (names : Std.HashSet Name) : Array Name := Id.run do
  let nameArray := names.toArray
  let mut deps : Std.HashMap Name (Array Name) := {}
  let mut inDegree : Std.HashMap Name Nat := {}
  for n in nameArray do
    inDegree := inDegree.insert n 0
  for n in nameArray do
    let d := directDepsInSet env n names
    deps := deps.insert n d
    for dep in d do
      inDegree := inDegree.insert dep ((inDegree.getD dep 0) + 1)
  let mut queue : Array Name := #[]
  for n in nameArray do
    if (inDegree.getD n 0) == 0 then
      queue := queue.push n
  let mut result : Array Name := #[]
  while !queue.isEmpty do
    let n := queue.back!
    queue := queue.pop
    result := result.push n
    for dep in (deps.getD n #[]) do
      let newDeg := (inDegree.getD dep 1) - 1
      inDegree := inDegree.insert dep newDeg
      if newDeg == 0 then
        queue := queue.push dep
  for n in nameArray do
    if !result.contains n then
      result := result.push n
  result.reverse

-- ═══ Phase 3: Per-command extraction ═══

/-- Classification of a command extracted from a source file. -/
inductive CmdClass where
  | tfbDecl (isSorried : Bool)   -- TFB declaration; `isSorried` = proof body replaced
  | context                      -- namespace/end/open/variable/section/set_option/universe
  | skip                         -- non-TFB declaration or other command
  deriving Inhabited, BEq

/-- A classified command with its source text.
    The Syntax kind is preserved so Phase 4 can distinguish namespace/open/variable/etc.
    without re-parsing the source string. -/
structure CommandEntry where
  cls : CmdClass
  src : String               -- source text (with sorry injection if applicable)
  kind : SyntaxNodeKind      -- the Syntax kind from the InfoTree
  deriving Inhabited

def findDeclVal? (root : Syntax) : Option (String.Pos.Raw × String.Pos.Raw) := Id.run do
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    let k := stx.getKind
    if k == ``Parser.Command.declValSimple ||
       k == ``Parser.Command.declValEqns ||
       k == ``Parser.Command.whereStructInst then
      match stx.getPos?, stx.getTailPos? with
      | some s, some e => return some (s, e)
      | _, _ => pure ()
    for arg in stx.getArgs do
      worklist := worklist.push arg
  return none

def hasSorryableKind (root : Syntax) : Bool := Id.run do
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    let k := stx.getKind
    if k == ``Parser.Command.theorem then
      return true
    for arg in stx.getArgs do
      worklist := worklist.push arg
  return false

def isContextCmd (stx : Syntax) : Bool :=
  let k := stx.getKind
  k == ``Parser.Command.namespace ||
  k == ``Parser.Command.«end» ||
  k == ``Parser.Command.open ||
  k == ``Parser.Command.variable ||
  k == ``Parser.Command.«section» ||
  k == ``Parser.Command.set_option ||
  k == ``Parser.Command.universe ||
  -- `attribute` is context, not a declaration. Dropping it silently changes
  -- what the emitted file means: `attribute [local instance]
  -- MvPolynomial.gradedAlgebra` is the only reason `CommRing` can be
  -- synthesised for a homogeneous localization, so without it every
  -- declaration built on that chart fails to elaborate.
  k == ``Parser.Command.attribute

def findDeclRanges? (env : Environment) (name : Name) : Option DeclarationRanges :=
  declRangeExt.find? (level := .exported) env name <|>
    declRangeExt.find? (level := .server) env name

/-- Process one source file: re-elaborate against project env, classify each command,
    extract source with sorry injection. Returns structured entries. -/
def processFile (source : String) (projectEnv : Environment)
    (tfbRangeMap : Std.HashMap String.Pos.Raw Name)
    (declPositions : Array String.Pos.Raw)
    (filePath : String) : IO (Array CommandEntry) := do
  let inputCtx := Parser.mkInputContext source filePath
  let (_, parserState, messages) ← Parser.parseHeader inputCtx
  let cmdState := { Command.mkState projectEnv messages {} with infoState.enabled := true }
  let finalState ← IO.processCommands inputCtx parserState cmdState
  let trees := finalState.commandState.infoState.trees.toArray
  let mut entries : Array CommandEntry := #[]
  for i in [:trees.size] do
    let tree := trees[i]!
    let cmdResult := tree.foldInfo (init := none) fun _ctx info acc =>
      match acc with
      | some _ => acc
      | none =>
        match info with
        | .ofCommandInfo ci => some ci.stx
        | _ => none
    let some stx := cmdResult | continue
    let some cmdStart := stx.getPos? | continue
    let some cmdEnd := stx.getTailPos? | continue
    let cmdSrc := (Substring.Raw.mk source cmdStart cmdEnd).toString
    let topKind := stx.getKind
    -- Skip header
    if topKind == ``Parser.Module.header then continue
    -- Match to TFB by byte position
    let mut declaredTFBName : Option Name := none
    for (pos, name) in tfbRangeMap do
      if pos >= cmdStart && pos < cmdEnd then
        declaredTFBName := some name
        break
    match declaredTFBName with
    | some tfbName =>
      let isThmInEnv := match projectEnv.find? tfbName with
        | some (.thmInfo _) => true
        | _ => false
      if hasSorryableKind stx || isThmInEnv then
        if let some (valStart, _) := findDeclVal? stx then
          let beforeVal := (Substring.Raw.mk source cmdStart valStart).toString
          entries := entries.push { cls := .tfbDecl true, src := beforeVal ++ " := sorry", kind := topKind }
        else
          entries := entries.push { cls := .tfbDecl true, src := cmdSrc, kind := topKind }
      else
        entries := entries.push { cls := .tfbDecl false, src := cmdSrc, kind := topKind }
    | none =>
      -- Denylist, not allowlist: drop non-TFB declarations, keep everything else.
      -- "Is this a declaration?" is answered by the environment, not by syntax
      -- kinds: `lemma` is a macro, so its kind is not `Parser.Command.declaration`,
      -- and the same is true of any user-defined declaration command. A command
      -- declares something iff some constant's `declRange` lies inside its span.
      let declaresSomething := declPositions.any fun pos => pos >= cmdStart && pos < cmdEnd
      if declaresSomething then
        entries := entries.push { cls := .skip, src := cmdSrc, kind := topKind }
      else
        entries := entries.push { cls := .context, src := cmdSrc, kind := topKind }
  return entries

-- ═══ Phase 4: Assembly ═══

/-- A module's classified content for assembly. -/
structure ModuleContent where
  modName : Name
  entries : Array CommandEntry
  deriving Inhabited

/-- Extract the "context signature" from a module's entries: the sequence of
    namespace/open/noncomputableSection commands (not variable/end/section). -/
def coreContextSignature (entries : Array CommandEntry) : Array SyntaxNodeKind := Id.run do
  let mut sig : Array SyntaxNodeKind := #[]
  for e in entries do
    match e.cls with
    | .context =>
      if e.kind == ``Parser.Command.namespace ||
         e.kind == ``Parser.Command.open then
        sig := sig.push e.kind
    | _ => pure ()
  sig

/-- Is this command one that opens a block closed by `end`? -/
private def isBlockOpener (kind : SyntaxNodeKind) : Bool :=
  kind == ``Parser.Command.«section» || kind == ``Parser.Command.namespace

/-- Whitespace-delimited tokens of `s`. -/
private def tokens (s : String) : List String :=
  ((((s.replace "\n" " ").replace "\t" " ").replace "\r" " ").splitOn " "
    ).filter (· != "")

/-- The identifier a block opener introduces, if any. `namespace Foo` and
`section Foo` are closed by `end Foo`; a bare `section` by `end`.
Scans for the keyword rather than assuming it starts the command: openers carry
modifiers (`noncomputable section`, `public section`) and attributes. -/
private def blockOpenerName (kind : SyntaxNodeKind) (src : String) : Option String :=
  let kw := if kind == ``Parser.Command.namespace then "namespace" else "section"
  match (tokens src).dropWhile (· != kw) with
  | _ :: name :: _ => some name
  | _ => none

/-- Remove empty block/end pairs from entries. A block is empty if it contains
    no TFB declarations between its `section`/`namespace` and its `end` — only
    variable/context commands. Uses Syntax kinds, not string parsing.

    `namespace` counts as a block opener, not just `section`. An emitted module
    routinely contains namespaces none of whose declarations made the closure,
    and such a namespace carries its `variable` bindings with it. Those
    bindings mention the very types that were excluded, so leaving the block in
    emits references to declarations that are not in the file. -/
def stripEmptySections (entries : Array CommandEntry) : Array CommandEntry := Id.run do
  let mut result : Array CommandEntry := #[]
  let mut i := 0
  while i < entries.size do
    let e := entries[i]!
    if isBlockOpener e.kind then
      -- Scan ahead tracking nesting depth. An empty block has no TFB decls
      -- at any nesting level before its matching end.
      let mut j := i + 1
      let mut hasTFBInside := false
      let mut depth := 1  -- we're inside one block
      while j < entries.size && depth > 0 do
        let ej := entries[j]!
        if isBlockOpener ej.kind then
          depth := depth + 1
        else if ej.kind == ``Parser.Command.«end» then
          depth := depth - 1
        else if let .tfbDecl _ := ej.cls then
          hasTFBInside := true
          break
        j := j + 1
      if !hasTFBInside && depth == 0 then
        -- Skip the entire section block (section + contents + matching end)
        i := j
      else
        result := result.push e
        i := i + 1
    else
      result := result.push e
      i := i + 1
  result

def emitStandalone (env : Environment) (rootPrefix : Name) (targetName : Name)
    (outputPath : System.FilePath)
    (excludePrefixes : Array Name := #[]) : IO Unit := do
  -- Phase 1: Determine target module and its imports.
  -- Import the target module's direct imports — these transitively cover all
  -- dependencies. Only declarations from the target's own module (or other
  -- non-imported modules) need to be emitted.
  let targetModName := match env.getModuleIdxFor? targetName with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => rootPrefix
  -- Get all modules transitively imported by the target module's imports
  let targetModIdx := env.getModuleIdx? targetModName
  let importedModules : Std.HashSet Name := Id.run do
    let mut imported : Std.HashSet Name := {}
    -- All modules with index < target module's index are imported by it
    -- (since moduleNames is in dependency-first order)
    if let some tIdx := targetModIdx then
      for i in [:tIdx.toNat] do
        imported := imported.insert env.header.moduleNames[i]!
    imported
  IO.eprintln s!"Target module: {targetModName}"
  IO.eprintln s!"Imported modules: {importedModules.size}"

  -- Phase 1b: TFB names — keep all project-local declarations.
  -- For a TFB audit, we want to show everything the reader must trust.
  let tfbNames ← match computeTFBNames env rootPrefix targetName excludePrefixes with
    | .ok names => pure names
    | .error msg => throw (IO.userError msg)
  IO.eprintln s!"TFB: {tfbNames.size} declarations"

  -- Phase 2: Module order from env.header.moduleNames (= import DAG order).
  -- Verified in Lean/Environment.lean:2120-2123: `importModulesCore` calls `goRec mod`
  -- (which recursively imports dependencies) BEFORE pushing the module name to
  -- `moduleNames`. So the array is in dependency-first topological order.
  let mut moduleSet : Std.HashSet Name := {}
  for name in tfbNames do
    if let some idx := env.getModuleIdxFor? name then
      moduleSet := moduleSet.insert env.header.moduleNames[idx.toNat]!
  let mut modIdxPairs : Array (Name × Nat) := #[]
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if moduleSet.contains modName then
      modIdxPairs := modIdxPairs.push (modName, i)
  let orderedModules := (modIdxPairs.qsort fun a b => a.2 < b.2).map (·.1)
  IO.eprintln s!"Emitting from {orderedModules.size} modules"

  -- Index every non-internal declaration by the module that declares it. Built
  -- once: this is the input to the "is this command a declaration?" test.
  -- No `isInternal` filter: private declarations carry mangled names, and if
  -- they are not in this index their commands are not recognised as
  -- declarations and leak into the skeleton as context.
  let mut namesByModule : Std.HashMap Name (Array Name) := {}
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if moduleSet.contains m then
        namesByModule := namesByModule.insert m ((namesByModule.getD m #[]).push n)

  -- Phase 3: Build tfbRangeMap per module and process each file
  let mut allModules : Array ModuleContent := #[]
  for modName in orderedModules do
    let filePath := modName.toString.replace "." "/" ++ ".lean"
    let source ← IO.FS.readFile filePath
    let fileMap := FileMap.ofString source
    let mut tfbRangeMap : Std.HashMap String.Pos.Raw Name := {}
    for name in tfbNames do
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]! == modName then
          if let some ranges := findDeclRanges? env name then
            let bytePos := fileMap.ofPosition ranges.range.pos
            tfbRangeMap := tfbRangeMap.insert bytePos name
    -- Every declaration in this module, TFB or not, so that a command can be
    -- recognised as a declaration regardless of which command defined it.
    let mut declPositions : Array String.Pos.Raw := #[]
    for name in (namesByModule.getD modName #[]) do
      if let some ranges := findDeclRanges? env name then
        declPositions := declPositions.push (fileMap.ofPosition ranges.range.pos)
    IO.eprintln s!"  {filePath} ({tfbRangeMap.size} TFB decls)"
    let entries ← processFile source env tfbRangeMap declPositions filePath
    -- Debug: dump section-related entries
    allModules := allModules.push { modName, entries := stripEmptySections entries }

  -- Phase 4: Assemble from structured entries
  -- Collect universes, set_options, opens, and noncomputable from context commands.
  -- Items that appear in every (or nearly every) module with TFB decls get hoisted.
  let tfbModules := allModules.filter fun mc =>
    mc.entries.any fun e => match e.cls with | .tfbDecl _ => true | _ => false
  let numTFBModules := tfbModules.size
  let mut setOptionCounts : Std.HashMap String Nat := {}
  let mut openCounts : Std.HashMap String Nat := {}
  let mut noncompCount : Nat := 0
  for mc in tfbModules do
    let mut seenOpts : Std.HashSet String := {}
    let mut seenOpens : Std.HashSet String := {}
    let mut hasNoncomp := false
    for e in mc.entries do
      match e.cls with
      | .context =>
        if e.kind == ``Parser.Command.set_option && !seenOpts.contains e.src then
          seenOpts := seenOpts.insert e.src
          setOptionCounts := setOptionCounts.insert e.src ((setOptionCounts.getD e.src 0) + 1)
        if e.kind == ``Parser.Command.open && !seenOpens.contains e.src then
          seenOpens := seenOpens.insert e.src
          openCounts := openCounts.insert e.src ((openCounts.getD e.src 0) + 1)
        if e.kind == ``Parser.Command.«section» && e.src.startsWith "noncomputable section" then
          hasNoncomp := true
      | _ => pure ()
    if hasNoncomp then noncompCount := noncompCount + 1
  -- Hoist set_options that appear in every TFB module
  let mut hoistedOpts : Array String := #[]
  for (src, count) in setOptionCounts do
    if count == numTFBModules then hoistedOpts := hoistedOpts.push src

  -- Emit header — import only external dependencies (e.g., Mathlib).
  -- Project-local modules are NOT imported; their TFB declarations are emitted.
  -- This ensures the standalone file shows all trusted declarations explicitly.
  -- `module` and the import list live in the module *header*, which is consumed
  -- by `parseHeader` and never reaches the command stream -- so unlike every
  -- other command it cannot be preserved by passing commands through. It has to
  -- be reconstructed. Dropping it is not cosmetic: outside a module-system file
  -- reducibility hints are computed over a different environment view, so the
  -- same definition with the same value and the same dependency heights is
  -- recorded with a different `ReducibilityHints.regular` height.
  let sourceIsModule : Bool := Id.run do
    let some idx := env.getModuleIdx? targetModName | return false
    return env.header.moduleData[idx.toNat]!.isModule
  let mut output := ""
  if sourceIsModule then
    output := output ++ "module\n\n"
  let importKw := if sourceIsModule then "public import" else "import"
  let mut emittedImports : Std.HashSet Name := {}
  -- Collect all imports from TFB modules that are external (not under rootPrefix)
  for modName in orderedModules do
    match env.getModuleIdx? modName with
    | some idx =>
      let imports := env.header.moduleData[idx.toNat]!.imports.map Import.module
      for imp in imports do
        if imp != `Init && !rootPrefix.isPrefixOf imp
          && !((`Informal).isPrefixOf imp) && !((`Stan).isPrefixOf imp) && !((`ProblemExtraction).isPrefixOf imp)
          && !emittedImports.contains imp then
          emittedImports := emittedImports.insert imp
          output := output ++ s!"{importKw} {imp}\n"
    | none => pure ()
  -- Also import direct imports of the target module that are external
  match env.getModuleIdx? targetModName with
  | some idx =>
    let imports := env.header.moduleData[idx.toNat]!.imports.map Import.module
    for imp in imports do
      if imp != `Init && !rootPrefix.isPrefixOf imp
          && !((`Informal).isPrefixOf imp) && !((`Stan).isPrefixOf imp) && !((`ProblemExtraction).isPrefixOf imp)
          && !emittedImports.contains imp then
        emittedImports := emittedImports.insert imp
        output := output ++ s!"{importKw} {imp}\n"
  | none => pure ()
  if emittedImports.isEmpty then
    output := output ++ s!"{importKw} Mathlib\n"
  output := output ++ "\n"
  output := output ++ "/-! # Trusted Formalization Base\n"
  output := output ++ s!"{rootPrefix} — `{targetName}`\n"
  output := output ++ s!"Auto-generated — all proofs replaced with `sorry`.\n"
  output := output ++ s!"{tfbNames.size} declarations in dependency order.\n"
  output := output ++ "-/\n\n"
  -- set_options are stripped entirely — they're project-specific and unnecessary
  -- for the standalone skeleton.
  output := output ++ "\n"

  -- Emit modules. Each module emits context + TFB declarations in source order.
  -- Hoisted set_options and universes are skipped. Spacing between sections.
  for mc in allModules do
    let hasTFB := mc.entries.any fun e => match e.cls with | .tfbDecl _ => true | _ => false
    if !hasTFB then continue
    let shortName := mc.modName.toString.drop (rootPrefix.toString.length + 1)
    output := output ++ s!"-- ═══ {shortName} ═══\n\n"
    -- Wrap each module in its own section and emit that module's `universe`
    -- command in place, rather than hoisting one union of universe names to the
    -- top of the file.
    --
    -- A declaration's `levelParams` are ordered by the enclosing `universe`
    -- command, restricted to the universes it uses. Modules legitimately differ
    -- here -- one may open `universe u v`, another `universe w v u` -- so no
    -- single hoisted line can reproduce every module's order. Hoisting silently
    -- permutes the universe parameters of the emitted declarations. The types
    -- still match up to renaming, so this is invisible to any check that
    -- compares types modulo universes, but Comparator compares statements
    -- exactly and rejects the skeleton.
    --
    -- The wrapper is required, not cosmetic: source files routinely declare
    -- `universe` at file scope with nothing enclosing it, and a file-scope
    -- `universe` in the concatenated output would collide with the next
    -- module's.
    output := output ++ "section\n"
    -- Openers this module leaves unclosed, outermost first. Source files
    -- commonly leave `noncomputable section` open to EOF, which is harmless in
    -- isolation but leaks across module boundaries once concatenated -- and
    -- would let one module's universes escape into the next.
    let mut openBlocks : Array (Option String) := #[]
    let mut prevWasDecl := false
    for e in mc.entries do
      match e.cls with
      | .context =>
        if isBlockOpener e.kind then
          openBlocks := openBlocks.push (blockOpenerName e.kind e.src)
        else if e.kind == ``Parser.Command.«end» then
          openBlocks := openBlocks.pop
        -- Add blank line before context that follows a declaration
        if prevWasDecl then output := output ++ "\n"
        output := output ++ e.src ++ "\n"
        prevWasDecl := false
      | .tfbDecl _ =>
        -- Add blank line before each declaration
        output := output ++ "\n"
        output := output ++ e.src ++ "\n"
        prevWasDecl := true
      | .skip => pure ()
    -- Close what the module left open, innermost first, then the wrapper.
    for closer in openBlocks.reverse do
      output := output ++ (match closer with | some n => s!"end {n}\n" | none => "end\n")
    output := output ++ "end\n"
    output := output ++ "\n"

  -- Strip `@[informal]` from output: it is the one attribute that requires
  -- importing `Informal`. `@[expose]` is core module-system syntax and must be
  -- preserved -- it changes how declarations are recorded.
  -- We identify them by string prefix since they're embedded in declaration source text,
  -- not separate commands.
  let lines := output.splitOn "\n"
  let filtered := lines.filter fun line =>
    let t := line.trimAsciiStart.toString
    !(t.startsWith "@[informal ")
  output := "\n".intercalate filtered
  -- Trim trailing whitespace
  output := output.trimAsciiEnd.toString ++ "\n"

  IO.FS.writeFile outputPath output
  IO.eprintln s!"Wrote {outputPath}"

end Stan.EmitStandalone

elab "#emit_standalone" root:ident target:ident path:str : command => do
  let env ← getEnv
  Stan.EmitStandalone.emitStandalone env root.getId target.getId path.getString

end
