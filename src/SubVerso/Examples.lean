/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Lean.Environment
public import Lean.Data.Options
public import Lean.Elab.Term
public import Lean.Elab.Command
public import SubVerso.Highlighting
import SubVerso.Compat
public meta import SubVerso.Compat
import SubVerso.Examples.Env
public meta import SubVerso.Examples.Env
import SubVerso.Examples.Messages
public section


namespace SubVerso.Examples

open Lean

meta def getSuppressed [Monad m] [MonadOptions m] : m (List Name) := do
  return (← getOptions) |> SubVerso.examples.suppressedNamespaces.get |>.splitOn " " |>.map (·.toName)

open SubVerso Highlighting

open Lean Elab Command Term

scoped syntax "%ex" "{" ident (" : " term)? "}" "{" term "}" : term
scoped syntax "%ex" "{" ident (" : " term)? "}" "{" docComment term "}" : term
scoped syntax "%ex" "{" ident "}" "{" tactic "}" : tactic
scoped syntax "%ex" "{" ident "}" "{" doElem "}" : doElem
scoped syntax "%ex" "{" ident "}" "{" term "}" : term

class MonadMessageState (m : Type → Type v) where
  getMessages : m MessageLog
  setMessages : MessageLog → m Unit

def savingNewTermMessages (act : TermElabM α) : TermElabM (α × MessageLog) := do
  let startMessages ← Core.getMessageLog
  Core.setMessageLog .empty
  try
    let res ← act
    let msgs ← Core.getMessageLog
    pure (res, msgs)
  finally
    Core.setMessageLog startMessages

meta def savingNewCommandMessages (act : CommandElabM α) : CommandElabM (α × MessageLog) := do
  let startMessages := (← get).messages
  modify ({· with messages := .empty})
  try
    let res ← act
    let msgs := (← get).messages
    pure (res, msgs)
  finally
    modify ({· with messages := startMessages})

scoped syntax (name:=exampleClassicConfig) "%example" ("(" &"config" " := " term")")? ident command command* "%end" : command

syntax exampleFlag := ("+" <|> "-") noWs ident
syntax exampleKind := "(" &"kind" " := " ident ")"
syntax exampleItem := exampleFlag <|> exampleKind

scoped syntax (name:=exampleSimpleConfig) "%example" exampleItem+ ident command command* "%end" : command

example : TermElabM Unit := logError "foo"

meta partial def extractExamples (stx : Syntax) : StateT (NameMap Syntax) Id Syntax := do
  if let `(term|%ex { $n:ident }{  $tm:term }%$tk) := stx then
    let next ← extractExamples tm
    -- Save the erased version in case there's nested examples
    let next := augmentTrailing next tk
    modify fun st => st.insert n.getId next
    pure next
  else if let `(term|%ex { $n:ident }{ $doc:docComment $tm:term }%$tk) := stx then
    let next ← extractExamples tm
    let next := augmentTrailing next tk
    modify fun st => st.insert n.getId doc
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

private meta def contents (message : Message) : IO String := do
  let head := if message.caption != "" then message.caption ++ ":\n" else ""
  pure <| withNewline <| head ++ (← message.data.toString)
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str

structure ExampleConfig where
  /-- This example contains an error -/
  error : Bool := false
  /-- This example should be thrown away after elaboration (implied by `error`) -/
  keep : Bool := true
  /--
  The example's output (info, warnings, and errors) should be logged even when there's no error to
  report.
  -/
  output : Bool := true
  /--
  If `true`, only embedded named examples are highlighted.
  -/
  embeddedOnly : Bool := false
  /--
  The example's kind, stored in the resulting environment.
  -/
  kind : Option Name := none


instance : Quote ExampleConfig where
  quote
    | ⟨error, keep, output, embeddedOnly, kind⟩ =>
      Syntax.mkCApp ``ExampleConfig.mk #[quote error, quote keep, quote output, quote embeddedOnly, quote kind]

meta def elabExampleConfig (stx : TSyntax `term) : TermElabM ExampleConfig := do
  match stx with
  | `({}) => pure {}
  | `({ $items:structInstField,* }) => mkConfig items.getElems {}
  | other => throwErrorAt other "Expected structure literal: {other}"
where
  asBool (stx : TSyntax `term) : TermElabM Bool := do
    match stx with
    | `($x:ident) =>
      match ← Compat.realizeNameNoOverloads x with
      | ``true => pure true
      | ``false => pure false
      | other => throwErrorAt stx "Expected Boolean literal, got {other}"
    | _ => throwErrorAt stx "Expected Boolean literal"
  asName (stx : TSyntax `term) : TermElabM Name := do
    match stx with
    | `($x:ident) =>
      pure x.getId.eraseMacroScopes
    | _ => throwErrorAt stx "Expected identifer"
  mkConfig (items : Array (TSyntax `Lean.Parser.Term.structInstField)) (config : ExampleConfig) : TermElabM ExampleConfig := do
    let mut config := config
    for item in items do
      if let `(Lean.Parser.Term.structInstField|$field:ident := $val:term) := item then
        if field.getId == `error then config := {config with error := ← asBool val}
        else if field.getId == `keep then config := {config with keep := ← asBool val}
        else if field.getId == `output then config := {config with output := ← asBool val}
        else if field.getId == `embeddedOnly then config := {config with embeddedOnly := ← asBool val}
        else if field.getId == `kind then config := {config with kind := ← asName val}
        else throwErrorAt field "Unknown field - expected 'error' or 'keep' or 'output'"
      else throwErrorAt item "Expected field initializer"
    pure config


meta def getSimpleExampleConfig (items : TSyntaxArray ``exampleItem) : TermElabM ExampleConfig := do
  let mut config : ExampleConfig := {}
  for item in items do
    match item with
    | `(exampleItem|(kind := $k)) => config := { config with kind := some k.getId.eraseMacroScopes }
    | `(exampleItem|+error) => config := { config with error := true }
    | `(exampleItem|+keep) => config := { config with keep := true }
    | `(exampleItem|+output) => config := { config with output := true }
    | `(exampleItem|+embeddedOnly) => config := { config with embeddedOnly := true }
    | `(exampleItem|-error) => config := { config with error := false }
    | `(exampleItem|-keep) => config := { config with keep := false }
    | `(exampleItem|-output) => config := { config with output := false }
    | `(exampleItem|-embeddedOnly) => config := { config with embeddedOnly := false }
    | other => throwErrorAt other "Unknown flag syntax - should start with '+' or '-'"
  pure config

macro_rules (kind := exampleClassicConfig)
  | `(%example $name:ident $cmd $cmds* %end) =>
    `(%example (config := {}) $name $cmd $cmds* %end)

private meta def saveExample
    [Monad m] [MonadEnv m] [MonadQuotation m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (name : Ident) (hl : Array Highlighted)
    (original : String) (start stop : Position)
    (messages : List (MessageSeverity × String))
    (kind : Option Name) : m Unit := do
  let mod ← getMainModule
  if let some forMod := (highlighted.getState (← getEnv)).find? mod then
    if let some ex := forMod.find? name.getId then
      logErrorAt name m!"Example '{name.getId}' already exists: {indentD (format ex)}"

  let ex := {
    highlighted := hl, original := original, start := start, stop := stop,
    messages := messages, kind := kind
  }
  modifyEnv fun ρ =>
    highlighted.addEntry ρ (mod, name.getId, ex)

/--
Transfers some of the trailing whitespace of stx1 to the leading whitespace of stx2. Only works when
`stx1` is original or canonical.

This is used to ensure that all the whitespace in the example is included in the example, as Lean's
own heuristic isn't quite the right thing here.
-/
meta partial def transferLines (stx1 stx2 : Syntax) : Syntax := Id.run do
  -- This needs to work in macros that expand to uses of `%example`, so it's not sufficient to
  -- require that stx1 be original (stx2 must be, or highlighting will fail). Instead, the start of
  -- `stx1`'s trailing whitespace is taken to be its end position, including in canonical synthetic
  -- nodes.

  let some stopPos := Compat.getInfoTailPos? stx1.getTailInfo (canonicalOnly := true)
    | return stx2
  let some leading := Compat.getInfoLeading? stx2.getHeadInfo
    | return stx2

  let mut iter : String.Iterator := ⟨leading.str, stopPos⟩
  while iter.pos < leading.startPos && iter.curr != '\n' do
    iter := iter.next
  if iter.pos ≥ leading.startPos then return stx2 -- no newlines found
  iter := iter.next -- found a newline, but don't include it in the example

  adjustLeading ({ · with startPos := iter.pos }) stx2
where
  adjustLeading (f : Substring → Substring) (stx : Syntax) : Syntax :=
    adjustLeading' f stx |>.getD stx
  adjustLeading' (f : Substring → Substring) : Syntax → Option Syntax
    | .missing => some .missing
    | .ident info rawVal x pre => some <| .ident (adjustInfo f info) rawVal x pre
    | .node info kind nodes => Id.run do
      let mut nodes' := #[]
      let mut done := false
      for n in nodes do
        if done then
          nodes' := nodes'.push n
        else if let some n' := adjustLeading' f n then
          nodes' := nodes'.push n'
          done := true
        else
          nodes' := nodes'.push n
      if done then
        some <| .node info kind nodes'
      else none
    | .atom info val => some <| .atom (adjustInfo f info) val
  adjustInfo (f : Substring → Substring) : SourceInfo → SourceInfo
    | .original leading pos trailing tailPos => .original (f leading) pos trailing tailPos
    | other => other

meta def elabExample
    (tok : Syntax) (config : ExampleConfig) (name : Ident) (allCommands : Array (TSyntax `command)) :
    CommandElabM Unit := Compat.commandWithoutAsync do
  let allCommands := allCommands.modify 0 (fun ⟨stx⟩ => ⟨transferLines name.raw stx⟩)
  let (allCommands, termExamples) := allCommands.mapM extractExamples .empty
  let initSt ← get

  let ((), newMessages) ← savingNewCommandMessages (allCommands.forM elabCommand)
  -- Run linters here, because elabCommandTopLevel would usually do it. This does mean examples
  -- will run linters multiple times, but it seems unavoidable while maintaining portability. Note
  -- that newMessages needs to be replayed into the main message log, but the linter messages must
  -- not be (or there will be duplicated linter output)
  let ((), linterMessages) ← savingNewCommandMessages (allCommands.forM runLinters)
  if config.error && !newMessages.hasErrors then
    throwErrorAt tok "Expected an error, but none occurred"
  let trees ← getInfoTrees
  let allNewMessages := newMessages ++ linterMessages
  let suppressedNS ← getSuppressed
  let hl ←
    if config.embeddedOnly then
      pure #[]
    else
      allCommands.mapM fun c => liftTermElabM (highlight c allNewMessages.toList.toArray trees suppressedNS)
  let freshMsgs ← allNewMessages.toList.mapM fun m => do pure (m.severity, ← contents m)
  let some b := allCommands[0]!.getPos?
    | throwErrorAt allCommands[0]! "Failed to get source position"
  let some b' := Compat.getLeadingHeadPos? allCommands[0]!
    | throwErrorAt allCommands[0]! "Failed to get source position"
  let some e := (Compat.Array.back! allCommands).getTailPos?
    | throwErrorAt (Compat.Array.back! allCommands) "Failed to get source position"
  let some e' := Compat.getTrailingTailPos? (Compat.Array.back! allCommands)
    | throwErrorAt (Compat.Array.back! allCommands) "Failed to get ending source position"

  let text ← getFileMap
  let str := Compat.String.Pos.extract text.source b' e'
  if config.error || !config.keep then set initSt
  saveExample name hl str (text.toPosition b) (text.toPosition e) freshMsgs config.kind

  for (tmName, term) in termExamples do
    let hl ← liftTermElabM (highlight term allNewMessages.toList.toArray trees suppressedNS)
    let .original leading startPos _ _ := term.getHeadInfo
      | throwErrorAt term "Failed to get source position"
    let .original _ _ trailing stopPos := term.getTailInfo
      | throwErrorAt term "Failed to get source position"
    let str := Compat.String.Pos.extract text.source leading.startPos trailing.stopPos
    saveExample (mkIdentFrom term <| name.getId ++ tmName) #[hl] str
      (text.toPosition startPos) (text.toPosition stopPos)
      freshMsgs (config.kind.map (· ++ `inner))

  -- If there's an unexpected error, always report output. Otherwise, follow the config.
  if (newMessages.hasErrors && !config.error) || config.output then
    let toReport := if config.error then newMessages.errorsToWarnings else newMessages
    for msg in toReport.toList ++ linterMessages.toList do
      logMessage msg

elab_rules : command
  | `(%example%$tk ( config := $cfg:term ) $name:ident $cmd $cmds* %end) => do
    let config ← liftTermElabM <| elabExampleConfig cfg
    elabExample tk config name (#[cmd] ++ cmds)

elab_rules (kind := exampleSimpleConfig) : command
  | `(%example%$tk $items* $name:ident $cmd $cmds* %end) => do
    let config ← liftTermElabM <| getSimpleExampleConfig items
    elabExample tk config name (#[cmd] ++ cmds)

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
private meta scoped instance : Quote Int where
  quote
    | .ofNat n => mkCApp ``Int.ofNat #[quote n]
    | .negSucc n => mkCApp ``Int.negSucc #[quote n]

open Syntax in
private meta def quoteJsonNumber : JsonNumber → Term
    | ⟨mantissa, exponent⟩ => mkCApp ``JsonNumber.mk #[quote mantissa, quote exponent]


meta instance : Quote JsonNumber where
  quote := private quoteJsonNumber


open Syntax in
meta partial instance : Quote Json where
  quote := q
where
  -- This funny quoting is because the RBMap quotes to an application of Json.mkObj, which is
  -- non-dependent
  quoteField {α : _} (_inst : Quote α) (f : (_ : String) × α) : TSyntax `term :=
    mkCApp ``Prod.mk #[quote f.fst, quote f.snd]
  quoteField' {α : _} (_inst : Quote α) (f : String × α) : TSyntax `term :=
    mkCApp ``Prod.mk #[quote f.fst, quote f.snd]
  q
    | .null => mkCApp ``Json.null #[]
    | .str s => mkCApp ``Json.str #[quote s]
    | .bool b => mkCApp ``Json.bool #[quote b]
    | .num n => mkCApp ``Json.num #[quote n]
    | .arr xs =>
      have : Quote Json := ⟨q⟩
      mkCApp ``Json.arr #[quote xs]
    | .obj fields =>
      have : Quote ((_ : String) × Json) := ⟨quoteField ⟨q⟩⟩
      have : Quote (String × Json) := ⟨quoteField' ⟨q⟩⟩
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
    let text ← getFileMap
    let .original leading startPos trailing stopPos := x.raw.getHeadInfo
      | throwErrorAt x "Failed to get source position"
    let str := Compat.String.Pos.extract text.source leading.startPos trailing.stopPos
    let suppressedNS ← getSuppressed
    let hl ← liftTermElabM <| highlight x #[] trees suppressedNS
    saveExample name #[hl] str (text.toPosition startPos) (text.toPosition stopPos) [] none

scoped syntax "%show_term " ("(" &"kind" " := " ident ")")? ident (":" term)? " := " term : command
elab_rules : command
  | `(%show_term $[(kind := $kind?)]? $x $[: $ty]? := $tm) => do
    let (tm, termExamples) := extractExamples tm {}

    liftTermElabM do
      let ty ← ty.mapM elabType
      let _ ← elabTerm tm ty
      synthesizeSyntheticMVarsNoPostponing

    let trees ← getInfoTrees
    let text ← getFileMap
    let .original leading startPos trailing stopPos := x.raw.getHeadInfo
      | throwErrorAt x "Failed to get source position"
    let str := Compat.String.Pos.extract text.source leading.startPos trailing.stopPos
    let suppressedNS ← getSuppressed
    let hl ← liftTermElabM <| highlight tm #[] trees suppressedNS
    let kind? := kind?.map (·.getId.eraseMacroScopes)

    saveExample x #[hl] str (text.toPosition startPos) (text.toPosition stopPos) [] kind?

    for (tmName, term) in termExamples do
      let hl ← liftTermElabM (highlight term #[] trees suppressedNS)
      let .original leading startPos _ _ := term.getHeadInfo
        | throwErrorAt term "Failed to get source position"
      let .original _ _ trailing stopPos := term.getTailInfo
        | throwErrorAt term "Failed to get source position"
      let str := Compat.String.Pos.extract text.source leading.startPos trailing.stopPos
      saveExample (mkIdentFrom term (x.getId ++ tmName)) #[hl] str (text.toPosition startPos) (text.toPosition stopPos) [] (kind?.map (· ++ `inner))

private meta def biDesc : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .instImplicit => "instance"
  | .strictImplicit => "strict implicit"


private meta partial def compare (blame : Syntax): Expr → Expr → MetaM Unit
  | .forallE x t1 b1 bi1, .forallE y t2 b2 bi2 => do
    if x.eraseMacroScopes != y.eraseMacroScopes then
      logErrorAt blame m!"Mismatched parameter name: expected '{x.eraseMacroScopes}' but got '{y.eraseMacroScopes}'"
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
/--
Check the signature by elaborating and comparing.
-/
meta def checkSignature
    (sigName : TSyntax `Lean.Parser.Command.declId)
    (sig : TSyntax `Lean.Parser.Command.declSig) :
    CommandElabM (Array Highlighting.Highlighted × String × Compat.String.Pos × Compat.String.Pos) := do
  let (sig, termExamples) := extractExamples sig .empty
  let sig : TSyntax `Lean.Parser.Command.declSig := ⟨sig⟩

  -- First make sure the names won't clash - we want two different declarations to compare.
  let mod ← getMainModule
  let sc ← getCurrMacroScope
  let addScope x := mkIdentFrom x (addMacroScope mod x.getId sc)
  let declName ← match sigName with
    | `(Lean.Parser.Command.declId|$x:ident) => pure x
    | `(Lean.Parser.Command.declId|$x:ident.{$_u:ident,*}) => pure x
    | _ => throwErrorAt sigName "Unexpected format of name: {sigName}"
  let (target, targetTrees) ← do
    let origTrees ← getResetInfoTrees
    let mut tgtTrees := PersistentArray.empty
    try
      let name ← liftTermElabM (Compat.realizeNameNoOverloads declName)
      tgtTrees ← getInfoTrees
      pure (name, tgtTrees)
    finally
      modifyInfoState ({· with trees := origTrees ++ tgtTrees})

  let noClash ← match sigName with
    | `(Lean.Parser.Command.declId|$x:ident) => `(Lean.Parser.Command.declId| $(addScope x):ident)
    | `(Lean.Parser.Command.declId|$x:ident.{$u:ident,*}) => `(Lean.Parser.Command.declId| $(addScope x):ident.{$u,*})
    | _ => throwErrorAt sigName "Unexpected format of name: {sigName}"

  -- Elaborate as an opaque constant (unsafe is to avoid an Inhabited constraint on the return type)
  let stx ← `(command| unsafe opaque $noClash $sig)
  let trees ← withoutModifyingEnv do
    let origTrees ← getResetInfoTrees
    let mut outTrees := PersistentArray.empty
    try
      elabCommand stx
      outTrees ← getInfoTrees
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
      pure outTrees
      finally
        modifyInfoState ({· with trees := origTrees ++ outTrees})

  -- Now actually generate the highlight
  let .original leading startPos _ _ := sigName.raw.getHeadInfo
    | throwErrorAt sigName "Failed to get source position"
  let .original _ _ trailing stopPos := sig.raw.getTailInfo
    | throwErrorAt sig.raw "Failed to get source position"
  let text ← getFileMap
  let suppressedNS ← getSuppressed
  let str := Compat.String.Pos.extract text.source leading.startPos trailing.stopPos
  let trees := targetTrees ++ trees
  let hl ← liftTermElabM <| withDeclName `x do
    pure <| #[← highlight sigName #[] trees suppressedNS, ← highlight sig #[] trees suppressedNS]

  for (tmName, term) in termExamples do
      let hl ← liftTermElabM (highlight term #[] trees suppressedNS)
      let .original leading startPos _ _ := term.getHeadInfo
        | throwErrorAt term "Failed to get source position"
      let .original _ _ trailing stopPos := term.getTailInfo
        | throwErrorAt term "Failed to get source position"
      let str := Compat.String.Pos.extract text.source leading.startPos trailing.stopPos
      saveExample (mkIdentFrom term (declName.getId ++ tmName)) #[hl] str (text.toPosition startPos) (text.toPosition stopPos) [] none

  return (hl, str, startPos, stopPos)

elab_rules : command
  | `(%signature $name $sigName $sig) => do
    let text ← getFileMap
    let (hl, str, startPos, stopPos) ← checkSignature sigName sig
    saveExample name hl str (text.toPosition startPos) (text.toPosition stopPos) [] none

open System in
meta partial def loadExamples
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
  -- libraries. Removing LEAN_GITHASH prevents it from getting into trace files in the subprocess.
  let lakeVars :=
    #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
      "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
      "LEAN_GITHASH",
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
        out := Compat.NameMap.mergeBy (fun _ j1 j2 => Compat.NameMap.mergeBy (fun _ _ x => x) j1 j2) out sub
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
                | .ok ex => out := out.insert name' (Compat.NameMap.get? out name' |>.getD {} |>.insert exName.toName ex)
      | _ => pure ()
    return out


%example -output test3
def wxyz (n : Nat) := 1 + 3 + n
#check wxyz
def xyz (n : Nat) := 1 + %ex{test2}{3 + n}
%end

%show_name Nat.rec
