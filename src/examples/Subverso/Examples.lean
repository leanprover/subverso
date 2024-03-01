import Subverso.Highlighting
import Subverso.Examples.Env
import Lean.Environment

namespace Subverso.Examples

open Subverso Highlighting

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
    setMessages (startMessages ++ endMessages)
  pure (res, endMessages)

scoped syntax "%example" ident command command* "%end" : command

example : TermElabM Unit := logError "foo"

partial def extractExamples (stx : Syntax) : StateT (NameMap Syntax) Id Syntax := do
  if let `(term|%ex { $n:ident }{ $tm:term }) := stx then
    let next ← extractExamples tm
    -- Save the erased version in case there's nested examples
    modify fun st => st.insert n.getId next
    pure next
  else
    match stx with
    | .node info kind args => pure <| .node info kind (← args.mapM extractExamples)
    | _ => pure stx

elab_rules : command
  | `(%example $name:ident $cmd $cmds* %end) => do
    let allCommands := #[cmd] ++ cmds
    let (allCommands, termExamples) := allCommands.mapM extractExamples .empty
    let ((), newMessages) ← savingNewMessages (allCommands.forM elabCommand)
    let trees ← getInfoTrees
    let hl ← allCommands.mapM fun c => liftTermElabM (highlight c newMessages.toList.toArray trees)
    let freshMsgs ← newMessages.toList.mapM fun m => do pure (m.severity, ← m.toString)
    let .original leading startPos _ _ := allCommands[0]!.getHeadInfo
      | throwErrorAt allCommands[0]! "Failed to get source position"
    let .original _ _ trailing stopPos := allCommands.back.getTailInfo
      | throwErrorAt allCommands.back "Failed to get source position"
    let text ← getFileMap
    let str := text.source.extract leading.startPos trailing.stopPos
    modifyEnv fun ρ => highlighted.addEntry ρ (name.getId, {highlighted := hl, original := str, start := text.toPosition startPos, stop := text.toPosition stopPos, messages := freshMsgs})
    for (name, term) in termExamples do
      let hl ← liftTermElabM (highlight term newMessages.toList.toArray trees)
      let .original leading startPos _ _ := term.getHeadInfo
        | throwErrorAt term "Failed to get source position"
      let .original _ _ trailing stopPos := term.getTailInfo
        | throwErrorAt term "Failed to get source position"
      let str := text.source.extract leading.startPos trailing.stopPos
      modifyEnv fun ρ => highlighted.addEntry ρ (name, {highlighted := #[hl], original := str, start := text.toPosition startPos, stop := text.toPosition stopPos, messages := freshMsgs})

scoped syntax "%dump" ident : command

elab_rules : command
  | `(%dump%$kw $name:ident) => do
    let st := highlighted.getState (← getEnv)
    if let some json := st.find? name.getId then
      logInfoAt kw m!"{toString json}"
    else
      throwErrorAt name "No highlighting found for '{name}'"

open System in
partial def loadExamples (leanProject : FilePath) : IO (NameMap Json) := do
  -- Validate that the path is really a Lean project
  let lakefile := leanProject / "lakefile.lean"
  if !(← lakefile.pathExists) then
    throw <| .userError s!"File {lakefile} doesn't exist, couldn't load project"
  -- Build the facet
  let res ← IO.Process.output {
    cmd := "lake"
    args := #["build", ":examples"]
    cwd := leanProject
  }
  if res.exitCode != 0 then
    throw <| .userError <|
      "Build process failed." ++
      decorateOut "stdout" res.stdout ++
      decorateOut "stderr" res.stderr
  let hlDir := leanProject / ".lake" / "build" / "examples"
  collectExamples .anonymous hlDir
where
  decorateOut (name : String) (out : String) : String :=
    if out.isEmpty then "" else s!"\n{name}:\n{out}\n"
  collectExamples (name : Name) (dir : FilePath) : IO (NameMap Json) := do
    let contents ← dir.readDir
    let mut out := {}
    for f in contents do
      match (← f.path.metadata).type with
      | .dir =>
        let sub ← collectExamples (.str name f.fileName) f.path
        out := out.mergeBy (fun _ _ j2 => j2) sub
      | .file =>
        if f.path.extension == some "json" then
          if let some mod := f.path.fileStem then
            let name' : Name := .str name mod
            let contents := Json.parse (← IO.FS.readFile f.path)
            match contents with
            | .error err => throw <| .userError s!"Couldn't parse {f.path} as JSON: {err}"
            | .ok val =>
              out := out.insert name' val
      | _ => pure ()
    return out


%example test3
def wxyz (n : Nat) := 1 + 3 + n
#check wxyz
def xyz (n : Nat) := 1 + %ex{test2}{3 + n}
%end

--%process_highlights

-- %example test
-- #eval 5
-- %end

-- %dump test
%dump test2
%dump test3
