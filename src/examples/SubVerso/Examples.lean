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
      modifyEnv fun ρ =>
        highlighted.addEntry ρ (mod, name.getId ++ tmName, {highlighted := #[hl], original := str, start := text.toPosition startPos, stop := text.toPosition stopPos, messages := freshMsgs})
    for msg in if config.error then newMessages.errorsToWarnings.toList else newMessages.toList do
      logMessage msg


scoped syntax "%dump " ident : command

elab_rules : command
  | `(%dump%$kw $name:ident) => do
    let mod ← getMainModule
    let st := highlighted.getState (← getEnv) |>.find? mod |>.getD {}
    if let some json := st.find? name.getId then
      logInfoAt kw m!"{toString json}"
    else
      throwErrorAt name "No highlighting found for '{name}'"

scoped syntax "%dump " ident &" into " ident: command
scoped syntax "%dumpE " ident &" into " ident: command

open Syntax in
private scoped instance : Quote Int where
  quote
    | .ofNat n => mkCApp ``Int.ofNat #[quote n]
    | .negSucc n => mkCApp ``Int.negSucc #[quote n]

open Syntax in
instance : Quote JsonNumber where
  quote
    | ⟨mantissa, exponent⟩ => mkCApp ``JsonNumber.mk #[quote mantissa, quote exponent]

open Syntax in
partial instance : Quote Json where
  quote := q
where
  quoteArray {α : _} (_inst : Quote α) (xs : Array α) : TSyntax `term :=
    mkCApp ``List.toArray #[quote xs.toList]
  quoteField {α : _} (_inst : Quote α) (f : (_ : String) × α) : TSyntax `term :=
    quote (f.fst, f.snd)
  q
    | .null => mkCApp ``Json.null #[]
    | .str s => mkCApp ``Json.str #[quote s]
    | .bool b => mkCApp ``Json.bool #[quote b]
    | .num n => mkCApp ``Json.num #[quote n]
    | .arr xs => mkCApp ``Json.arr #[(quoteArray ⟨q⟩ xs)]
    | .obj fields =>
      let _fieldInst : Quote ((_ : String) × Json) := ⟨quoteField ⟨q⟩⟩
      let fieldList := quote fields.toArray.toList
      mkCApp ``Json.mkObj #[fieldList]

elab_rules : command
  | `(%dump $name:ident into $x) => do
    let mod ← getMainModule
    let st := highlighted.getState (← getEnv) |>.find? mod |>.getD {}
    if let some json := st.find? name.getId then
      elabCommand <| ← `(def $x : Json := $(quote json))
    else
      throwErrorAt name "No highlighting found for '{name}'"

open Syntax in
instance : Quote MessageSeverity where
  quote s :=
    let n :=
      match s with
      | .error => ``MessageSeverity.error
      | .information => ``MessageSeverity.information
      | .warning => ``MessageSeverity.warning
    mkCApp n #[]

open Syntax in
instance : Quote Lean.Position where
  quote s :=
    mkCApp ``Lean.Position.mk #[quote s.line, quote s.column]

open Syntax in
instance : Quote Example where
  quote ex :=
    mkCApp ``Example.mk #[quote ex.highlighted, quote ex.messages, quote ex.original, quote ex.start, quote ex.stop]

elab_rules : command
  | `(%dumpE $name:ident into $x) => do
    let mod ← getMainModule
    let st := highlighted.getState (← getEnv) |>.find? mod |>.getD {}
    if let some json := st.find? name.getId then
      match FromJson.fromJson? json with
      | .ok (e : Example) =>
        elabCommand <| ← `(def $x : Example := $(quote e))
      | .error err =>
        throwErrorAt name "Couldn't deserialize JSON: {err}"
    else
      throwErrorAt name "No highlighting found for '{name}'"


namespace Internals
scoped syntax "%show_name" ident : term
elab_rules : term
  | `(%show_name $x) => do
    let _ ← Compat.realizeNameNoOverloads x
    elabTerm (← `((() : Unit))) none

end Internals

scoped syntax "%show_name" ident (&"as" ident)? : command

macro_rules
  | `(%show_name $x) => `(%show_name $x as $x)

open Internals in
elab_rules : command
  | `(%show_name $x as $name) => do
    elabCommand <| ← `(def helper := %show_name $x)
    let trees ← getInfoTrees
    let mod ← getMainModule
    let text ← getFileMap
    let .original leading startPos trailing stopPos := x.raw.getHeadInfo
      | throwErrorAt x "Failed to get source position"
    let str := text.source.extract leading.startPos trailing.stopPos
    let hl ← liftTermElabM <| highlight x #[] trees
    modifyEnv fun ρ =>
      highlighted.addEntry ρ (mod, name.getId, {highlighted := #[hl], original := str, start := text.toPosition startPos, stop := text.toPosition stopPos, messages := []})

private def biDesc : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .instImplicit => "instance"
  | .strictImplicit => "strict implicit"


private partial def compare (blame : Syntax): Expr → Expr → MetaM Unit
  | .forallE x t1 b1 bi1, .forallE y t2 b2 bi2 => do
    if x != y then logErrorAt blame m!"Mismatched parameter name: expected '{x}' but got '{y}'"
    if bi1 != bi2 then logErrorAt blame m!"Mismatched binder of {x}: expected {biDesc bi1} but got {biDesc bi2}"
    if t1.isAppOfArity' ``optParam 2 then
      if t2.isAppOfArity' ``optParam 2 then
        if !(← Meta.isDefEq t1.appArg! t2.appArg!) then
          logErrorAt blame m!"Mismatched default values for parameter {x}: expected '{t1.appArg!}' but got '{t2.appArg!}'"
    Meta.withLocalDecl x bi1 t1 fun e =>
      compare blame (b1.instantiate1 e) (b2.instantiate1 e)
  | .mdata _ tty', sty => compare blame tty' sty
  | tty , .mdata _ sty' => compare blame tty sty'
  | _, _ => pure ()

scoped syntax (name := signature) "%signature" ident declId declSig : command
elab_rules : command
  | `(%signature $name $sigName $sig) => do
    -- Check the signature by elaborating and comparing.

    -- First make sure the names won't clash - we want two different declarations to compare.
    let mod ← getMainModule
    let sc ← getCurrMacroScope
    let addScope x := mkIdentFrom x (addMacroScope mod x.getId sc)
    let declName ← match sigName with
      | `(Lean.Parser.Command.declId|$x:ident) => pure x
      | `(Lean.Parser.Command.declId|$x:ident.{$u:ident,*}) => pure x
      | _ => throwErrorAt sigName "Unexpected format of name: {sigName}"
    let target ← liftTermElabM <| Compat.realizeNameNoOverloads declName
    let noClash ← match sigName with
      | `(Lean.Parser.Command.declId|$x:ident) => `(Lean.Parser.Command.declId| $(addScope x):ident)
      | `(Lean.Parser.Command.declId|$x:ident.{$u:ident,*}) => `(Lean.Parser.Command.declId| $(addScope x):ident.{$u,*})
      | _ => throwErrorAt sigName "Unexpected format of name: {sigName}"

    -- Elaborate as an opaque constant (unsafe is to avoid an Inhabited constraint on the return type)
    let stx ← `(command| unsafe opaque $noClash $sig)
    withoutModifyingEnv do
      elabCommand stx
      if ← MonadLog.hasErrors then throwErrorAt sigName "Failed to elaborate signature"

      -- The "source" is what the user wrote, the "target" is the existing declaration
      let source ← liftTermElabM <| Compat.realizeNameNoOverloads (addScope declName)
      let ti ← getConstInfo target
      let si ← getConstInfo source
      if si.numLevelParams != ti.numLevelParams then
        throwErrorAt sigName "Mismatched number of level params: {target} has {ti.numLevelParams}, not {si.numLevelParams}"
      let lvls := ti.levelParams.map mkLevelParam
      let te : Expr := .const target lvls
      let se : Expr := .const source lvls
      liftTermElabM do
        let tty ← Meta.inferType te
        let sty ← Meta.inferType se
        if !(← Meta.isDefEq tty sty) then
          throwErrorAt sig "Expected {tty}, got {sty}"
        compare sigName tty sty

    -- Now actually generate the highlight and save it
    let .original leading startPos _ _ := sigName.raw.getHeadInfo
      | throwErrorAt sigName "Failed to get source position"
    let .original _ _ trailing stopPos := sig.raw.getTailInfo
      | throwErrorAt sig.raw "Failed to get source position"
    let text ← getFileMap
    let str := text.source.extract leading.startPos trailing.stopPos
    let trees ← getInfoTrees
    let hl ← liftTermElabM <| withDeclName `x <| do pure <| #[← highlight sigName #[] trees, ← highlight sig #[] trees]
    modifyEnv fun ρ =>
      highlighted.addEntry ρ (mod, name.getId, {highlighted := hl, original := str, start := text.toPosition startPos, stop := text.toPosition stopPos, messages := []})


open System in
partial def loadExamples
    (leanProject : FilePath)
    (overrideToolchain : Option String := none) : IO (NameMap (NameMap Example)) := do
  let projectDir := ((← IO.currentDir) / leanProject).normalize
  -- Validate that the path is really a Lean project
  let lakefile := projectDir / "lakefile.lean"
  let lakefile' := projectDir / "lakefile.toml"
  if !(← lakefile.pathExists) && !(← lakefile'.pathExists) then
    throw <| .userError s!"Neither {lakefile} nor {lakefile'} exist, couldn't load project"
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
        if f.path.extension == some "json" && f.path.fileStem.map (·.takeRight 4) != some ".log" then
          if let some mod := f.path.fileStem then
            let name' : Name := .str modName mod
            let contents := Json.parse (← IO.FS.readFile f.path)
            match contents with
            | .error err => throw <| .userError s!"Couldn't parse {f.path} as JSON: {err}"
            | .ok val =>
              let .ok o := val.getObj?
                | throw <| IO.userError s!"Expected JSON object in '{f.path}', got {val}"
              for ⟨exName, exJson⟩ in o.toArray do
                match FromJson.fromJson? (α := Example) exJson with
                | .error err => throw <| IO.userError s!"Couldn't deserialize example '{exName}': {err}"
                | .ok ex => out := out.insert name' (out.find? name' |>.getD {} |>.insert exName.toName ex)
      | _ => pure ()
    return out


%example test3
def wxyz (n : Nat) := 1 + 3 + n
#check wxyz
def xyz (n : Nat) := 1 + %ex{test2}{3 + n}
%end

%show_name Nat.rec
