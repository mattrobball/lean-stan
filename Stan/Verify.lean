/-
Copyright (c) 2025 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard, Formalization
-/
module

public meta import Lean

/-!
# Post-condition: does the emitted file say what the project says?

The emitter reconstructs each declaration's elaboration environment from its
source. That reconstruction can be wrong in ways that still compile: a dropped
`set_option` changes how proofs inside public signatures are lifted, a hoisted
`universe` command permutes `levelParams`, a missing `module` header changes
the reducibility hints a definition is recorded with. Every one of those
produces a file that builds cleanly and states something other than what was
proved.

So the emitter checks itself. `verifyEmitted` elaborates the file it just
wrote, in a fresh environment built from that file's own imports, and compares
every declaration it produced against the same declaration in the project.

Comparison is up to binder names, which differ by hygiene: the same `variable`
binder is named after whichever module elaborated it. Everything else --
`levelParams` and their order, the type, and a definition's value -- must
agree exactly.

`ReducibilityHints` is reported but never fails the check. It is an unfolding
heuristic, not mathematical content, and a tool comparing declarations for
equality of *meaning* has no business rejecting on it.
-/

public meta section

open Lean Elab

namespace Stan.Verify

/-- Erase binder names so that alpha-equivalent terms compare equal. Hygienic
binder names embed the module that elaborated them, so they differ between the
project and the emitted file by construction. -/
partial def eraseBinderNames : Expr → Expr
  | .forallE _ d b bi => .forallE `_ (eraseBinderNames d) (eraseBinderNames b) bi
  | .lam _ d b bi     => .lam `_ (eraseBinderNames d) (eraseBinderNames b) bi
  | .letE _ t v b nd  => .letE `_ (eraseBinderNames t) (eraseBinderNames v) (eraseBinderNames b) nd
  | .app f a          => .app (eraseBinderNames f) (eraseBinderNames a)
  | .mdata _ e        => eraseBinderNames e
  | .proj s i e       => .proj s i (eraseBinderNames e)
  | e                 => e

/-- What differed, for one declaration. -/
structure Mismatch where
  name    : Name
  field   : String
  project : String
  emitted : String

def hintStr : ReducibilityHints → String
  | .opaque => "opaque" | .abbrev => "abbrev" | .regular n => s!"regular {n}"

/-- Compare one emitted declaration against the project's. -/
def compareConst (projectEnv : Environment) (n : Name) (emitted : ConstantInfo) :
    Array Mismatch × Option Mismatch := Id.run do
  let mut hard : Array Mismatch := #[]
  let some proj := projectEnv.find? n
    | return (#[{ name := n, field := "presence"
                , project := "absent", emitted := "declared" }], none)
  if proj.levelParams != emitted.levelParams then
    hard := hard.push { name := n, field := "levelParams"
                      , project := toString proj.levelParams
                      , emitted := toString emitted.levelParams }
  let pt := eraseBinderNames proj.type
  let et := eraseBinderNames emitted.type
  if pt != et then
    hard := hard.push { name := n, field := "type"
                      , project := toString pt, emitted := toString et }
  -- A definition's value is part of what it means; a theorem's is not, and the
  -- emitted one is `sorry` by design.
  match proj, emitted with
  | .defnInfo pd, .defnInfo ed =>
    let pv := eraseBinderNames pd.value
    let ev := eraseBinderNames ed.value
    if pv != ev then
      hard := hard.push { name := n, field := "value"
                        , project := toString pv, emitted := toString ev }
    if pd.hints != ed.hints then
      return (hard, some { name := n, field := "hints"
                         , project := hintStr pd.hints, emitted := hintStr ed.hints })
  | _, _ => pure ()
  return (hard, none)

/-- Elaborate `outputPath` in a fresh environment built from its own imports,
and compare every declaration it produces against `projectEnv`.

Returns `true` if the emitted file faithfully reproduces the project. -/
def verifyEmitted (projectEnv : Environment) (outputPath : System.FilePath) : IO Bool := do
  let source ← IO.FS.readFile outputPath
  let inputCtx := Parser.mkInputContext source outputPath.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← Elab.processHeader header {} messages inputCtx
  if messages.hasErrors then
    IO.eprintln "verify: the emitted file's header does not elaborate"
    for m in messages.toList do IO.eprintln (← m.toString)
    return false
  let cmdState := Command.mkState env messages {}
  let finalState ← IO.processCommands inputCtx parserState cmdState
  let msgs := finalState.commandState.messages
  if msgs.hasErrors then
    IO.eprintln "verify: the emitted file does not elaborate"
    for m in msgs.toList do
      if m.severity == .error then IO.eprintln (← m.toString)
    return false
  -- `map₂` holds exactly the constants this file declared; `map₁` is imports.
  let emittedEnv := finalState.commandState.env
  let mut hard : Array Mismatch := #[]
  let mut soft : Array Mismatch := #[]
  let mut checked := 0
  for (n, ci) in emittedEnv.constants.map₂ do
    if n.isInternal then continue
    checked := checked + 1
    let (h, s) := compareConst projectEnv n ci
    hard := hard ++ h
    if let some s := s then soft := soft.push s
  IO.eprintln s!"verify: compared {checked} declarations against the project"
  unless soft.isEmpty do
    IO.eprintln s!"verify: {soft.size} reducibility-hint difference(s) (not a failure):"
    for m in soft do
      IO.eprintln s!"  {m.name}: project {m.project}, emitted {m.emitted}"
  if hard.isEmpty then
    IO.eprintln "verify: OK — the emitted file states what the project states"
    return true
  IO.eprintln s!"verify: FAILED — {hard.size} mismatch(es)"
  for m in hard do
    IO.eprintln s!"  {m.name} [{m.field}]"
    IO.eprintln s!"    project: {m.project}"
    IO.eprintln s!"    emitted: {m.emitted}"
  return false

end Stan.Verify

end
