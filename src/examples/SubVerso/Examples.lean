import SubVerso.Highlighting
import SubVerso.Compat
import SubVerso.Examples.Env
import Lean.Environment

namespace SubVerso.Examples

open SubVerso Highlighting

open Lean Elab Command Term

scoped syntax "%ex" "{" ident (" : " term)? "}" "{" term "}" : term
scoped syntax "%ex" "{" ident "}" "{" tactic "}" : tactic
scoped syntax "%ex" "{" ident "}" "{" doElem "}" : doElem


class MonadMessageState (m : Type → Type v) where
  getMessages : m MessageLog
  setMessages : MessageLog → m Unit

instance : MonadMessageState TermElabM where
  getMessages := do return (← getThe Core.State).messages
  setMessages msgs := modifyThe Core.State ({· with messages := msgs})

instance : MonadMessageState CommandElabM where
  getMessages := do return (← get).messages
  setMessages msgs := modify ({· with messages := msgs})

open MonadMessageState in
def savingNewMessages [Monad m] [MonadFinally m] [MonadMessageState m]
    (act : m α) : m (α × MessageLog) := do
  let startMessages ← getMessages
  let mut endMessages := .empty
  setMessages .empty
  let res ← try
    let res ← act
    endMessages ← getMessages
    pure res
  finally
    setMessages startMessages
  pure (res, endMessages)

scoped syntax "%example" ("(" &"config" " := " term")")? ident command command* "%end" : command

example : TermElabM Unit := logError "foo"

partial def extractExamples (stx : Syntax) : StateT (NameMap Syntax) Id Syntax := do
  if let `(term|%ex { $n:ident }{ $tm:term }%$tk) := stx then
    let next ← extractExamples tm
    -- Save the erased version in case there's nested examples
    let next := augmentTrailing next tk
    modify fun st => st.insert n.getId next
    pure next
  else
    match stx with
    | .node info kind args => pure <| .node info kind (← args.mapM extractExamples)
    | _ => pure stx
where
  getTrailing (stx : Syntax) : String :=
    match stx.getTailInfo with
    | .original _ _ t _ => t.toString
    | _ => ""
  augmentTrailing (stx tok : Syntax) : Syntax :=
    stx.updateTrailing (getTrailing stx ++ getTrailing tok).toSubstring

private def contents (message : Message) : IO String := do
  let head := if message.caption != "" then message.caption ++ ":\n" else ""
  pure <| withNewline <| head ++ (← message.data.toString)
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str

structure ExampleConfig where
  /-- This example contains an error -/
  error : Bool := false
  /-- This example should be thrown away after elaboration (implied by `error`) -/
  keep : Bool := true

def elabExampleConfig (stx : TSyntax `term) : TermElabM ExampleConfig :=
  match stx with
  | `({}) => pure {}
  | `({ $items:structInstField,* }) => mkConfig items.getElems {}
  | other => throwErrorAt other "Expected structure literal"
where
  asBool (stx : TSyntax `term) : TermElabM Bool := do
    match stx with
    | `($x:ident) =>
      match ← Compat.realizeNameNoOverloads x with
      | ``true => pure true
      | ``false => pure false
      | other => throwErrorAt stx "Expected Boolean literal, got {other}"
    | _ => throwErrorAt stx "Expected Boolean literal"
  mkConfig (items : Array (TSyntax `Lean.Parser.Term.structInstField)) (config : ExampleConfig) : TermElabM ExampleConfig := do
    let mut config := config
    for item in items do
      if let `(Lean.Parser.Term.structInstField|$field:ident := $val:term) := item then
        if field.getId == `error then config := {config with error := ← asBool val}
        else if field.getId == `keep then config := {config with keep := ← asBool val}
        else throwErrorAt field "Unknown field - expected 'error' or 'keep'"
      else throwErrorAt item "Exptected field initializer"
    pure config

macro_rules
  | `(%example $name:ident $cmd $cmds* %end) => `(%example (config := {}) $name $cmd $cmds* %end)

deriving instance Repr for MessageSeverity

elab_rules : command
  | `(%example%$tk ( config := $cfg:term ) $name:ident $cmd $cmds* %end) => do
    let config ← liftTermElabM <| elabExampleConfig cfg
    let allCommands := #[cmd] ++ cmds
    let (allCommands, termExamples) := allCommands.mapM extractExamples .empty
    let initSt ← get
    let ((), newMessages) ← savingNewMessages (allCommands.forM elabCommand)
    if config.error && !newMessages.hasErrors then
      throwErrorAt tk "Expected an error, but none occurred"
    let trees ← getInfoTrees
    let hl ← allCommands.mapM fun c => liftTermElabM (highlight c newMessages.toList.toArray trees)
    let freshMsgs ← newMessages.toList.mapM fun m => do pure (m.severity, ← contents m)
    let .original leading startPos _ _ := allCommands[0]!.getHeadInfo
      | throwErrorAt allCommands[0]! "Failed to get source position"
    let .original _ _ trailing stopPos := allCommands.back.getTailInfo
      | throwErrorAt allCommands.back "Failed to get source position"
    let text ← getFileMap
    let str := text.source.extract leading.startPos trailing.stopPos
    let mod ← getMainModule
    if config.error || !config.keep then set initSt
    modifyEnv fun ρ => highlighted.addEntry ρ (mod, name.getId, {highlighted := hl, original := str, start := text.toPosition startPos, stop := text.toPosition stopPos, messages := freshMsgs})
    for (tmName, term) in termExamples do
      let hl ← liftTermElabM (highlight term newMessages.toList.toArray trees)
      let .original leading startPos _ _ := term.getHeadInfo
        | throwErrorAt term "Failed to get source position"
      let .original _ _ trailing stopPos := term.getTailInfo
        | throwErrorAt term "Failed to get source position"
      let str := text.source.extract leading.startPos trailing.stopPos
      modifyEnv fun ρ => highlighted.addEntry ρ (mod, name.getId ++ tmName, {highlighted := #[hl], original := str, start := text.toPosition startPos, stop := text.toPosition stopPos, messages := freshMsgs})
    for msg in if config.error then newMessages.errorsToWarnings.toList else newMessages.toList do
      logMessage msg


scoped syntax "%dump" ident : command

elab_rules : command
  | `(%dump%$kw $name:ident) => do
    let mod ← getMainModule
    let st := highlighted.getState (← getEnv) |>.find? mod |>.getD {}
    if let some json := st.find? name.getId then
      logInfoAt kw m!"{toString json}"
    else
      throwErrorAt name "No highlighting found for '{name}'"

open System in
partial def loadExamples
    (leanProject : FilePath)
    (overrideToolchain : Option String := none) : IO (NameMap (NameMap Example)) := do
  let projectDir := ((← IO.currentDir) / leanProject).normalize
  -- Validate that the path is really a Lean project
  let lakefile := projectDir / "lakefile.lean"
  if !(← lakefile.pathExists) then
    throw <| .userError s!"File {lakefile} doesn't exist, couldn't load project"
  let toolchain ← match overrideToolchain with
    | none =>
      let toolchainfile := projectDir / "lean-toolchain"
      if !(← toolchainfile.pathExists) then
        throw <| .userError s!"File {toolchainfile} doesn't exist, couldn't load project"
      pure (← IO.FS.readFile toolchainfile).trim
    | some override => pure override

  -- Kludge: remove variables introduced by Lake. Clearing out DYLD_LIBRARY_PATH and
  -- LD_LIBRARY_PATH is useful so the version selected by Elan doesn't get the wrong shared
  -- libraries.
  let lakeVars :=
    #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
      "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
      "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]

  let cmd := "elan"
  let args := #["run", "--install", toolchain, "lake", "build", ":examples"]

  -- Build the facet
  let res ← IO.Process.output {
    cmd, args, cwd := projectDir
    -- Unset Lake's environment variables
    env := lakeVars.map (·, none)
  }
  if res.exitCode != 0 then
    IO.eprintln <|
      "Build process failed." ++
      "\nCWD: " ++ projectDir.toString ++
      "\nCommand: " ++ cmd ++
      "\nArgs: " ++ repr args ++
      "\nExit code: " ++ toString res.exitCode ++
      "\nstdout: " ++ res.stdout ++
      "\nstderr: " ++ res.stderr

    throw <| .userError <|
      "Build process failed." ++
      decorateOut "stdout" res.stdout ++
      decorateOut "stderr" res.stderr
  let hlDir := leanProject / ".lake" / "build" / "examples"
  collectExamples .anonymous hlDir
where
  decorateOut (name : String) (out : String) : String :=
    if out.isEmpty then "" else s!"\n{name}:\n{out}\n"
  collectExamples (modName : Name) (dir : FilePath) : IO (NameMap (NameMap Example)) := do
    let contents ← dir.readDir
    let mut out := {}
    for f in contents do
      match (← f.path.metadata).type with
      | .dir =>
        let sub ← collectExamples (.str modName f.fileName) f.path
        out := out.mergeBy (fun _ j1 j2 => j1.mergeBy (fun _ _ x => x) j2) sub
      | .file =>
        if f.path.extension == some "json" then
          if let some mod := f.path.fileStem then
            let name' : Name := .str modName mod
            let contents := Json.parse (← IO.FS.readFile f.path)
            match contents with
            | .error err => throw <| .userError s!"Couldn't parse {f.path} as JSON: {err}"
            | .ok val =>
              let .ok o := val.getObj?
                | throw <| IO.userError "Expected JSON object in '{f.path}'"
              for ⟨exName, exJson⟩ in o.toArray do
                match FromJson.fromJson? (α := Example) exJson with
                | .error err => throw <| IO.userError s!"Couldn't deserialized example: {err}"
                | .ok ex => out := out.insert name' (out.find? name' |>.getD {} |>.insert exName.toName ex)
      | _ => pure ()
    return out


%example test3
def wxyz (n : Nat) := 1 + 3 + n
#check wxyz
def xyz (n : Nat) := 1 + %ex{test2}{3 + n}
%end
