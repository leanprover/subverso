
import SubVerso.Examples
import SubVerso.Highlighting.Highlighted
import SubVerso.Highlighting.Anchors
import SubVerso.Highlighting.String

/-! These are SubVerso tests that don't involve a subprocess, to make development easier. -/


open SubVerso Examples

partial def SubVerso.Highlighting.Highlighted.asString (hl : Highlighted) : String := Id.run do
  let mut out := ""
  match hl with
  | .seq hls =>
    for x in hls.map asString do
      out := out ++ x
  | .span _ hl' =>
    out := out ++ hl'.asString
  | .tactics _ _ _ hl' =>
    out := out ++ hl'.asString
  | .point .. => pure ()
  | .text s => out := out ++ s
  | .unparsed s => out := out ++ s
  | .token t => out := out ++ t.content
  out


partial def SubVerso.Highlighting.Highlighted.proofStates (hl : Highlighting.Highlighted) : Array (String × Array (Goal String)) := Id.run do
  let mut out := #[]
  match hl with
  | .seq hls =>
    for x in hls.map proofStates do
      out := out ++ x
  | .span _ hl' =>
    out := out ++ hl'.proofStates
  | .tactics info _ _ hl' =>
    out := out.push (hl'.asString, info.map (·.map (·.asString)))
  | _ => pure ()
  out

set_option pp.rawOnError true

%example proof
theorem test (n : Nat) : n * 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    cases n
    next => simp
    case' succ =>
      skip
    case succ =>
      . skip; simp
%end

%dump proof into proofJson

%dumpE proof into proofEx

%example proof2
example :
    (fun (x y z : Nat) =>
      x + (y + z))
    =
    (fun x y z =>
      (z + x) + y)
  := by
  conv =>
    lhs
    intro x y z
    conv =>
      arg 2
      rw [Nat.add_comm]
    rw [← Nat.add_assoc]
    arg 1
    rw [Nat.add_comm]
%end

%dumpE proof2 into proofEx2


-- We don't have #guard_msgs in all supported Lean versions, so here's a low-tech replacement:

open Lean Elab Command in
elab "#evalString" s:str e:term : command => do
  let msgs := (← get).messages
  try
    modify ({· with messages := {}})
    elabCommand <| ← `(#eval $e)
    let msgs' := (← get).messages
    let [msg] := msgs'.toList
      | throwError "Too many messages:\n{msgs'.toArray.map (·.data)}"
    if (← msg.toString) != s.getString then
      throwErrorAt e "Expected {String.quote s.getString}, got {String.quote (← msg.toString)}"
  finally
    modify ({· with messages := msgs})

open Lean Elab Command in
elab "#evalStrings " "[" ss:str,* "] " e:term : command => do
  let msgs := (← get).messages
  try
    modify ({· with messages := {}})
    elabCommand <| ← `(#eval $e)
    let msgs' := (← get).messages
    let [msg] := msgs'.toList
      | throwError "Too many messages:\n{msgs'.toArray.map (·.data)}"
    let ok := ss.getElems.toList.map (·.getString)
    if (← msg.toString) ∉ ok then
      throwErrorAt e "Expected one of {ok.map String.quote}, got {String.quote (← msg.toString)}"
  finally
    modify ({· with messages := msgs})

#evalString "[[\"n * 1 = n\"]]\n"
  (proofEx.highlighted.proofStates.toList.filter (·.fst == "by") |>.map (·.snd.toList.map (·.conclusion)))

#evalStrings [ -- NB #5677 changed goal displays, so the second
               -- version here became the expected output after
               -- nightly-2024-10-18.
    "[[some \"zero\"], [some \"succ\"], [none], [some \"succ.succ\"], [none]]\n",
    "[[none], [some \"succ.succ\"], [none]]\n"]
 (proofEx.highlighted.proofStates.toList.filter (·.fst == "=>") |>.map (·.snd.toList.map (·.name)))

/-! # Message Normalization -/

open SubVerso.Examples.Messages

private def ex1 :=
"(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
             n k
1) 743:19-32 ≤ =
"

#evalString "\"(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)\\n             n k\\n1) L1:19-32 ≤ =\\n\"\n"
 (normalizeLineNums ex1)

private def ex2 :=
"(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
             n k
1) 843:19-32 ≤ =
2) 843:19-32 ≤ =
2) 943:19-32 ≤ =
2) 843:143-32 ≤ =
"

#evalString "\"(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)\\n             n k\\n1) L1:19-32 ≤ =\\n2) L1:19-32 ≤ =\\n2) L2:19-32 ≤ =\\n2) L1:143-32 ≤ =\\n\"\n"
  (normalizeLineNums ex2)

#evalString "\"List ?m.1\"\n"
  (normalizeMetavars "List ?m.9783")

#evalString "\"Type ?u.1\"\n" (normalizeMetavars "Type ?u.9783")

#evalString "\"Type ?x.9783\"\n" (normalizeMetavars "Type ?x.9783")

#evalString "\"List ?m.1 \"\n" (normalizeMetavars "List ?m.9783 ")

#evalString "\"x : ?m.1\\nxs : List ?m.1\\nelem : x ∈ xs\\n⊢ xs.length > 0\\n\"\n"
(normalizeMetavars
"x : ?m.1034
xs : List ?m.1034
elem : x ∈ xs
⊢ xs.length > 0
")

#evalString "\"x : ?m.1\\nα : Type ?u.2\\nxs : List ?m.3\\nelem : x ∈ xs\\n⊢ xs.length > 0\"\n"
(normalizeMetavars
"x : ?m.1035
α : Type ?u.1234
xs : List ?m.1034
elem : x ∈ xs
⊢ xs.length > 0")


section
open SubVerso.Highlighting

#evalString "some (\"foo\", true)\n" (anchor? "-- ANCHOR: foo").toOption

#evalString "some (\"foo\", true)\n" (anchor? "-- ANCHOR:foo").toOption

#evalString "some (\"foo\", true)\n" (anchor? "           -- ANCHOR:    foo").toOption

#evalString "some (\"foo\", false)\n" (anchor? "-- ANCHOR_END: foo").toOption

#evalString "some (\"foo\", false)\n" (anchor? "-- ANCHOR_END:foo").toOption

#evalString "some (\"foo\", false)\n" (anchor? "           -- ANCHOR_END:    foo").toOption

#evalString "none\n" (anchor? "           -- ANCHOR_END :    foo").toOption

end

/-! # Highlighting Unparsed Spans -/
section HighlightUnparsed

partial def hlStringWithMessages : Highlighting.Highlighted → String
  | .seq xs => xs.foldl (init := "") (fun s hl => s ++ hlStringWithMessages hl)
  | .point k s => s!"[point {k}: {s.toString}]"
  | .tactics _ _ _ x => hlStringWithMessages x
  | .span info x =>
    let labels := info.map fun (k, s) => s!"{k}: {s.toString}"
    let labelStr := ", ".intercalate labels.toList
    s!"[{labelStr}]({hlStringWithMessages x})"
  | .text s | .token ⟨_, s⟩ | .unparsed s => s

open Lean Elab Command in
def highlightWithPrefixedMessages (input : String) (msgPrefix := "subverso_test") :
    CommandElabM Highlighting.Highlighted := do
  let inputCtx := Parser.mkInputContext input "<input>"
  let commandState : Command.State := {
    env := (← getEnv)
    maxRecDepth := (← get).maxRecDepth
  }
  let (result, { commandState, commands, .. }) ← Compat.Frontend.processCommands mkNullNode
    |>.run { inputCtx } |>.run { commandState, parserState := {}, cmdPos := 0 }
  let result := result.items.filter (·.commandSyntax.getKind != ``Lean.Parser.Command.eoi)
  let mut hls : Highlighting.Highlighted := .empty
  let mut lastPos : Compat.String.Pos := 0
  let allMessages := result.map (·.messages.toArray) |>.flatten
  for cmd in result do
    let hl ← runTermElabM fun _ =>
      withTheReader Core.Context (fun ctx => { ctx with fileMap := inputCtx.fileMap }) do
        let msgs ← allMessages.filterM fun msg =>
          return (← msg.toString).startsWith msgPrefix
        Highlighting.highlightIncludingUnparsed cmd.commandSyntax (startPos? := lastPos)
          msgs cmd.info
    lastPos := Compat.getTrailingTailPos? cmd.commandSyntax |>.getD lastPos
    hls := hls ++ hl
  return hls

/--
`#evalHighlight inp exp` highlights `inp` using the including-unparsed
highlighter and checks that the result matches `exp`, where only messages
beginning with the prefix "subverso_test" are included (to avoid version
discrepancies).
-/
elab "#evalHighlight" inp:str exp:str : command => do
  let input := inp.getString
  let hl ← highlightWithPrefixedMessages input
  let expected := exp.getString
  let hlStr := hlStringWithMessages hl
  if hlStr != expected then
    throwError m!"Mismatched output\n---Found:---\n{hlStr}\n\n---Expected:---\n{expected}"

#evalHighlight "deriving a bunch of other filler text def b := true

def inject (start fin : Nat) (str : String) : Lean.Elab.Command.CommandElabM Unit := do
  let stx := Lean.Syntax.atom (.synthetic ⟨start⟩ ⟨fin⟩) (String.mk [])
  Lean.logInfoAt stx str

elab \"inject_info\" : command => do
  inject 0 16 \"subverso_test: 1\"
  inject 20 25 \"subverso_test: 2\"
  inject 26 26 \"subverso_test: 3\"
  inject 20 43 \"subverso_test: 4\"
  inject 33 43 \"subverso_test: 5\"

inject_info"
  "[info: subverso_test: 1](deriving a bunch) of [info: subverso_test: 4]([info: subverso_test: 2](other) [info: subverso_test: 3](filler) [info: subverso_test: 5](text def b)) := true

def inject (start fin : Nat) (str : String) : Lean.Elab.Command.CommandElabM Unit := do
  let stx := Lean.Syntax.atom (.synthetic ⟨start⟩ ⟨fin⟩) (String.mk [])
  Lean.logInfoAt stx str

elab \"inject_info\" : command => do
  inject 0 16 \"subverso_test: 1\"
  inject 20 25 \"subverso_test: 2\"
  inject 26 26 \"subverso_test: 3\"
  inject 20 43 \"subverso_test: 4\"
  inject 33 43 \"subverso_test: 5\"

inject_info"

#evalHighlight "def x := (· ++ ·)" "def x := (· ++ ·)"

end HighlightUnparsed

section

open Lean Elab Command in
def highlightFromString (input : String) : CommandElabM Highlighting.Highlighted := do
  let inputCtx := Parser.mkInputContext input "<input>"
  let commandState : Command.State := {
    env := (← getEnv)
    maxRecDepth := (← get).maxRecDepth
  }
  let (_, { commandState, commands, .. }) ← Frontend.processCommands
    |>.run { inputCtx } |>.run { commandState, parserState := {}, cmdPos := 0 }
  let mut hls : Highlighting.Highlighted := .empty
  for stx in commands do
    let hl ← runTermElabM fun _ =>
      withTheReader Core.Context (fun ctx => { ctx with fileMap := inputCtx.fileMap }) do
        let msgs := commandState.messages.toArray
        unless msgs.isEmpty do
          throwError "Unwanted messages: {← msgs.mapM (·.toString)}"
        Highlighting.highlight stx msgs commandState.infoState.trees
    hls := hls ++ hl
  return hls

open Lean Elab Command in
/--
Highlights `input` via the module path (`highlightFrontendResult` with `pp.tagAppFns` set), the way
`subverso-extract-mod` does. This produces the tactic-region structure that per-command highlighting
doesn't, so it exercises comment trivia inside proof tactics.
-/
def highlightModuleStyleSegments (input : String) : CommandElabM (Array Highlighting.Highlighted) := do
  let inputCtx := Parser.mkInputContext input "<input>"
  let (headerStx, parserState, msgs) ← Parser.parseHeader inputCtx
  let commandState : Command.State :=
    { env := (← getEnv), maxRecDepth := (← get).maxRecDepth, messages := msgs }
  let commandState :=
    let sc := commandState.scopes[0]!
    { commandState with scopes := { sc with opts := sc.opts.setBool `pp.tagAppFns true } :: commandState.scopes.tail! }
  let (result, _) ← Compat.Frontend.processCommands headerStx
    |>.run { inputCtx } |>.run { commandState, parserState, cmdPos := parserState.pos }
  let result := result.updateLeading input
  runTermElabM fun _ =>
    withTheReader Core.Context (fun ctx => { ctx with fileMap := inputCtx.fileMap }) do
      Highlighting.highlightFrontendResult result

open Lean Elab Command in
@[inherit_doc highlightModuleStyleSegments]
def highlightModuleStyle (input : String) : CommandElabM Highlighting.Highlighted := do
  return (← highlightModuleStyleSegments input).foldl (· ++ ·) .empty

open Lean Elab Command in
-- Each frontend item's messages are the command's own parse errors and elaboration messages, even
-- when the previous command's message range ends exactly where the command starts.
#eval show CommandElabM Unit from do
  let inputCtx := Parser.mkInputContext "#check (1)#check (2)" "<input>"
  let commandState : Command.State := { env := (← getEnv), maxRecDepth := (← get).maxRecDepth }
  let (result, _) ← Compat.Frontend.processCommands mkNullNode
    |>.run { inputCtx } |>.run { commandState, parserState := {}, cmdPos := 0 }
  let items := result.items.filter (·.commandSyntax.getKind != ``Lean.Parser.Command.eoi)
  let logs ← items.mapM fun i => do
    let msgs ← Compat.messageLogArray i.messages |>.mapM (·.toString)
    pure <| String.join msgs.toList
  unless logs.size == 2 do
    throwError m!"Expected 2 items, got {logs.size}"
  let contains (s pat : String) : Bool := (s.splitOn pat).length > 1
  unless contains logs[0]! "1 : Nat" && !(contains logs[0]! "2 : Nat") do
    throwError m!"First item's messages are wrong: {logs[0]!}"
  unless contains logs[1]! "2 : Nat" && !(contains logs[1]! "1 : Nat") do
    throwError m!"Second item's messages are wrong: {logs[1]!}"

open Lean Elab Command in
-- A message logged at a synthetic position inside another command's range is rendered on the code
-- it points at.
#eval show CommandElabM Unit from do
  let hl ← highlightModuleStyle <|
    "def target := 55\n\n" ++
    "def inject (start fin : Nat) (str : String) : Lean.Elab.Command.CommandElabM Unit := do\n" ++
    "  let stx := Lean.Syntax.atom (.synthetic ⟨start⟩ ⟨fin⟩) (String.mk [])\n" ++
    "  Lean.logInfoAt stx str\n\n" ++
    "elab \"inject_info\" : command => do\n" ++
    "  inject 4 10 \"subverso_test_pool\"\n\n" ++
    "inject_info"
  let out := hlStringWithMessages hl
  unless (out.splitOn "[info: subverso_test_pool](target)").length > 1 do
    throwError m!"Missing pooled message span:\n{out}"

open Lean Elab Command in
-- Empty and comment-only modules highlight cleanly.
#eval show CommandElabM Unit from do
  for input in ["", "\n\n  \n", "-- only a comment\n"] do
    let hl ← highlightModuleStyle input
    if hl.hasError then
      throwError m!"Error span highlighting {repr input}:\n{hlStringWithMessages hl}"

open Lean Elab Command in
-- A parse error in a file with no commands is rendered.
#eval show CommandElabM Unit from do
  let hl ← highlightModuleStyle "/- foo"
  unless hl.hasError do
    throwError m!"Missing error span:\n{hlStringWithMessages hl}"

open Lean Elab Command in
-- A parse error at the end of the file is rendered in the truncated command's segment.
#eval show CommandElabM Unit from do
  let hls ← highlightModuleStyleSegments "def foo :="
  unless hls.size == 3 do
    throwError m!"Expected header, command, and end-of-input segments, got {hls.size}"
  unless hls[1]!.hasError do
    throwError m!"The truncated command lacks its error span"
  if hls[2]!.hasError then
    throwError m!"The error span landed on the end-of-input item"

open Lean Elab Command in
-- A message whose range ends exactly where the next command starts is rendered once, on the
-- command that produced it.
#eval show CommandElabM Unit from do
  let hl ← highlightModuleStyle "example : Nat := \"hi\"#check 2"
  let out := hlStringWithMessages hl
  let errorSpans := (out.splitOn "[error:").length - 1
  unless errorSpans == 1 do
    throwError m!"Expected one error span, got {errorSpans}:\n{out}"

/--
`#evalHighlight inp exp` highlights `inp` using the including-unparsed
highlighter and checks that the result matches `exp`, where only messages
beginning with the prefix "subverso_test" are included (to avoid version
discrepancies).
-/
elab "#evalHighlight'" inp:str exp:str : command => do
  let input := inp.getString
  let hl ← highlightFromString input
  let expected := exp.getString
  let hlStr := hlStringWithMessages hl
  if hlStr != expected then
    throwError m!"Mismatched output\n---Found:---\n{hlStr}\n\n---Expected:---\n{expected}"

-- Check that the · regression is fixed
#evalHighlight' "def x : String → String → String := (· ++ ·)" "def x : String → String → String := (· ++ ·)"

end

/-! # Token kinds -/
section TokenKinds
open SubVerso.Highlighting

namespace SubVerso.Highlighting

/-- The name of a token kind's constructor, for use in assertions (payloads are ignored). -/
def Token.Kind.name : Token.Kind → String
  | .keyword .. => "keyword"
  | .delim .. => "delim"
  | .const .. => "const"
  | .anonCtor .. => "anonCtor"
  | .var .. => "var"
  | .wildcard .. => "wildcard"
  | .str .. => "str"
  | .option .. => "option"
  | .docComment => "docComment"
  | .sort .. => "sort"
  | .levelVar .. => "levelVar"
  | .levelOp .. => "levelOp"
  | .levelConst .. => "levelConst"
  | .moduleName .. => "moduleName"
  | .withType .. => "withType"
  | .num .. => "num"
  | .char .. => "char"
  | .lineComment => "lineComment"
  | .blockComment => "blockComment"
  | .commentDelim => "commentDelim"
  | .operator .. => "operator"
  | .bracket .. => "bracket"
  | .separator .. => "separator"
  | .unknown => "unknown"

/-- Collects all tokens of a highlighted tree, in source order. -/
partial def Highlighted.tokenList (hl : Highlighted) : Array Token := Id.run do
  let mut out := #[]
  match hl with
  | .seq hls => for x in hls do out := out ++ x.tokenList
  | .span _ hl' => out := hl'.tokenList
  | .tactics _ _ _ hl' => out := hl'.tokenList
  | .token t => out := #[t]
  | _ => pure ()
  return out

/-- Collects all unparsed source segments in source order. -/
partial def Highlighted.unparsedList (hl : Highlighted) : Array String := Id.run do
  let mut out := #[]
  match hl with
  | .seq hls => for x in hls do out := out ++ x.unparsedList
  | .span _ hl' => out := hl'.unparsedList
  | .tactics _ _ _ hl' => out := hl'.unparsedList
  | .unparsed s => out := #[s]
  | _ => pure ()
  return out

/-- Whether the highlighted tree contains a `.tactics` (proof-state) wrapper. -/
partial def Highlighted.hasTactics : Highlighted → Bool
  | .tactics .. => true
  | .seq hls => hls.any Highlighted.hasTactics
  | .span _ hl => hl.hasTactics
  | _ => false

/-- The occurrence tag of a production-bearing token kind, if any. -/
def Token.Kind.occurrence? : Token.Kind → Option String
  | .keyword _ occ _ | .delim _ occ _ | .operator _ occ _ | .bracket _ occ _ | .separator _ occ _ => occ
  | _ => none

/-- Whether a token survives a `ToJson`/`FromJson` round-trip unchanged. -/
def Token.jsonRoundtrips (t : Token) : Bool :=
  match (Lean.fromJson? (Lean.toJson t) : Except String Token) with
  | .ok t' => t' == t
  | .error _ => false

end SubVerso.Highlighting

open Lean Elab Command in
/--
`#assertKind inp content kind` highlights `inp` and checks that every token whose content equals
`content` has the given kind constructor name. Errors if no such token exists.
-/
elab "#assertKind" inp:str content:str kind:str : command => do
  let hl ← highlightFromString inp.getString
  let toks := hl.tokenList
  let matching := toks.filter (·.content == content.getString)
  if matching.isEmpty then
    let all := toks.toList.map fun t => (t.content, t.kind.name)
    throwError m!"No token with content {repr content.getString}. Tokens: {repr all}"
  for t in matching do
    if t.kind.name != kind.getString then
      throwError m!"Token {repr t.content} has kind {t.kind.name}, expected {kind.getString}"

open Lean Elab Command in
/-- `#assertHasKind inp kind` highlights `inp` and checks that at least one token has `kind`. -/
elab "#assertHasKind" inp:str kind:str : command => do
  let hl ← highlightFromString inp.getString
  let toks := hl.tokenList
  unless toks.any (·.kind.name == kind.getString) do
    let all := toks.toList.map fun t => (t.content, t.kind.name)
    throwError m!"No token of kind {kind.getString}. Tokens: {repr all}"

open Lean Elab Command in
/--
`#assertAnchor inp name expected` highlights `inp` (so comments are tokenized), runs the anchor
extractor, and checks that the anchor `name` exists and its code equals `expected` exactly
(untrimmed — the surrounding whitespace is part of what these tests protect). This guards that
`-- ANCHOR:`/`-- ANCHOR_END:` directives are still recognized after comment tokenization.
-/
elab "#assertAnchor" inp:str name:str expected:str : command => do
  let hl ← highlightFromString inp.getString
  match hl.anchored with
  | .error e => throwError m!"anchored failed: {e}"
  | .ok ex =>
    match Compat.HashMap.get? ex.anchors name.getString with
    | none => throwError m!"No anchor named {repr name.getString}"
    | some a =>
      -- Compare the exact (untrimmed) anchor code, so a stray leading/trailing newline is caught.
      if a.toString != expected.getString then
        throwError m!"Anchor {repr name.getString} = {repr a.toString}, expected {repr expected.getString}"

open Lean Elab Command in
/--
Checks that, after the anchor pass, `ex.code` still contains a `.lineComment` token with `content`.
Guards that a comment which merely *looks* like a directive (e.g. trailing one) keeps its token
styling rather than being flattened to text.
-/
elab "#assertAnchorKeepsComment" inp:str content:str : command => do
  let hl ← highlightFromString inp.getString
  match hl.anchored with
  | .error e => throwError m!"anchored failed: {e}"
  | .ok ex =>
    unless ex.code.tokenList.any (fun t => t.kind.name == "lineComment" && t.content == content.getString) do
      throwError m!"anchored code lost the lineComment token {repr content.getString}"

open Lean Elab Command in
/--
Like `#assertAnchorKeepsComment`, but checks `ex.code` for a token of an arbitrary `kind` (e.g.
`blockComment`, `docComment`) with `content`. The anchored extractor must leave such comments
untouched.
-/
elab "#assertAnchorCodeHasToken" inp:str kind:str content:str : command => do
  let hl ← highlightFromString inp.getString
  match hl.anchored with
  | .error e => throwError m!"anchored failed: {e}"
  | .ok ex =>
    unless ex.code.tokenList.any (fun t => t.kind.name == kind.getString && t.content == content.getString) do
      throwError m!"anchored code lost the {kind.getString} token {repr content.getString}"

open Lean Elab Command in
/-- Checks that the numeral with `content` carries the inferred type `expectedType`. -/
elab "#assertNumType" inp:str content:str expectedType:str : command => do
  let hl ← highlightWithPrefixedMessages inp.getString
  let toks := hl.tokenList.filter (·.content == content.getString)
  if toks.isEmpty then throwError m!"no token with content {repr content.getString}"
  for t in toks do
    match t.kind with
    | .num (some ty) _ =>
      if ty != expectedType.getString then
        throwError m!"numeral {repr content.getString} has type {repr ty}, expected {repr expectedType.getString}"
    | .num none _ => throwError m!"numeral {repr content.getString} has no inferred type"
    | _ => throwError m!"token {repr content.getString} is not a numeral"

open Lean Elab Command in
/-- Checks that the wildcard `_` with `content` is a `.wildcard` carrying the inferred `expectedType`. -/
elab "#assertWildcardType" inp:str content:str expectedType:str : command => do
  let hl ← highlightWithPrefixedMessages inp.getString
  let toks := hl.tokenList.filter (·.content == content.getString)
  if toks.isEmpty then throwError m!"no token with content {repr content.getString}"
  for t in toks do
    match t.kind with
    | .wildcard ty _ =>
      if ty != expectedType.getString then
        throwError m!"wildcard {repr content.getString} has type {repr ty}, expected {repr expectedType.getString}"
    | _ => throwError m!"token {repr content.getString} is not a wildcard (is {t.kind.name})"

open Lean Elab Command in
/-- Highlights `inp` with tactic info and checks the anchor pass found a proof state named `name`. -/
elab "#assertProofState" inp:str name:str : command => do
  let hl ← highlightWithPrefixedMessages inp.getString
  match hl.anchored with
  | .error e => throwError m!"anchored failed: {e}"
  | .ok ex =>
    unless (Compat.HashMap.get? ex.proofStates name.getString).isSome do
      throwError m!"no proof state named {repr name.getString}"

open Lean Elab Command in
/-- Checks that `anchored` on the highlighting of `inp` fails with a message starting with `expected`. -/
elab "#assertAnchorError" inp:str expected:str : command => do
  let hl ← highlightFromString inp.getString
  match hl.anchored with
  | .ok _ => throwError m!"expected anchored to fail ({repr expected.getString}), but it succeeded"
  | .error e =>
    unless expected.getString.isPrefixOf e do
      throwError m!"anchored error {repr e} does not start with {repr expected.getString}"

open Lean Elab Command in
/--
Checks that the token(s) with `content` carry an occurrence tag that is not attributed to an
anonymous `null` grouping node (regression guard for null-node transparency).
-/
elab "#assertOccurrenceNotNull" inp:str content:str : command => do
  let hl ← highlightFromString inp.getString
  let matching := hl.tokenList.filter (·.content == content.getString)
  if matching.isEmpty then throwError m!"no token with content {repr content.getString}"
  for t in matching do
    match t.kind.occurrence? with
    | some occ =>
      if occ.startsWith "null" then
        throwError m!"token {repr t.content} ({t.kind.name}) has a null-based occurrence {repr occ}"
    | none => throwError m!"token {repr t.content} ({t.kind.name}) has no occurrence"

open Lean Elab Command in
/-- Checks that `inp` highlights to a `.char` token whose decoded character equals `expected`. -/
elab "#assertCharValue" inp:str expected:str : command => do
  let hl ← highlightFromString inp.getString
  let chars := hl.tokenList.filterMap fun t =>
    match t.kind with | .char c => some c.toString | _ => none
  unless chars.contains expected.getString do
    throwError m!"char tokens decoded to {repr chars.toList}, expected to contain {repr expected.getString}"

open Lean Elab Command in
/-- Checks that every name in `names` is among the names that highlighting `input` marks as defined. -/
def assertDefines (input : String) (names : List Name) : CommandElabM Unit := do
  let hl ← highlightWithPrefixedMessages input
  let defined := hl.definedNames
  for name in names do
    unless defined.contains name do
      throwError m!"{name} is not marked as defined. Defined names: {defined.toList}"

open Lean Elab Command in
@[inherit_doc assertDefines]
elab "#assertDefines" inp:str names:str* : command => do
  assertDefines inp.getString (names.toList.map (·.getString.toName))

open Lean Elab Command in
/--
Like `#assertKind`, but highlights through the info-recording (Compat-frontend, includes-unparsed)
path so that semantic info — e.g. an applied constructor in `⟨1, 2⟩` — is available, mirroring real
extraction (`subverso-extract-mod`).
-/
elab "#assertKindRich" inp:str content:str kind:str : command => do
  let hl ← highlightWithPrefixedMessages inp.getString
  let toks := hl.tokenList
  let matching := toks.filter (·.content == content.getString)
  if matching.isEmpty then
    let all := toks.toList.map fun t => (t.content, t.kind.name)
    throwError m!"No token with content {repr content.getString}. Tokens: {repr all}"
  for t in matching do
    if t.kind.name != kind.getString then
      throwError m!"Token {repr t.content} has kind {t.kind.name}, expected {kind.getString}"

open Lean Elab Command in
/-- Checks that the includes-unparsed highlighter still emits a non-trivia source gap as `.unparsed`. -/
elab "#assertRichHasUnparsed" inp:str content:str : command => do
  let hl ← highlightWithPrefixedMessages inp.getString
  unless hl.unparsedList.contains content.getString do
    throwError m!"unparsed segments = {repr hl.unparsedList.toList}, expected {repr content.getString}"

open Lean Elab Command in
/-- Checks that the includes-unparsed highlighter does not emit a token with this content and kind. -/
elab "#assertRichLacksToken" inp:str content:str kind:str : command => do
  let hl ← highlightWithPrefixedMessages inp.getString
  let found := hl.tokenList.any fun t => t.content == content.getString && t.kind.name == kind.getString
  if found then
    let all := hl.tokenList.toList.map fun t => (t.content, t.kind.name)
    throwError m!"unexpected token {repr content.getString}/{kind.getString}. Tokens: {repr all}"

open Lean Elab Command in
/-- Checks that the includes-unparsed highlighter emits no `.unparsed` segment. -/
elab "#assertRichNoUnparsed" inp:str : command => do
  let hl ← highlightWithPrefixedMessages inp.getString
  unless hl.unparsedList.isEmpty do
    throwError m!"unexpected unparsed segments = {repr hl.unparsedList.toList}"

-- Numerals (decimal, hex, scientific) are `.num`
#assertKind "def n := 42" "42" "num"
#assertKind "def n := 0xff" "0xff" "num"
#assertKind "def n := 1.5e3" "1.5e3" "num"
-- A numeral carries its inferred type (read from its own info), including non-trivial types.
#assertNumType "def n := 42" "42" "Nat"
#assertNumType "def n : Fin 5 := 3" "3" "Fin 5"

-- Character literals are `.char`, carrying the *decoded* character (escapes resolved)
#assertKind "def c := 'a'" "'a'" "char"
#assertCharValue "def c := 'a'" "a"
#assertCharValue "def c := '\\n'" "\n"

open Lean Elab Command in
/--
Checks that the token with `content` is a `.str` whose `interpolation` flag equals `expected`
(`"true"`/`"false"`).
-/
elab "#assertStrInterpolation" inp:str content:str expected:str : command => do
  let hl ← highlightFromString inp.getString
  let toks := hl.tokenList.filter (·.content == content.getString)
  if toks.isEmpty then throwError m!"no token with content {repr content.getString}"
  let want := expected.getString == "true"
  for t in toks do
    match t.kind with
    | .str _ interp =>
      if interp != want then
        throwError m!"string {repr content.getString} has interpolation {interp}, expected {want}"
    | _ => throwError m!"token {repr content.getString} is not a string (is {t.kind.name})"

-- A complete string literal is a `.str` that is *not* part of an interpolation.
#assertKind "def s := \"hello\"" "\"hello\"" "str"
#assertStrInterpolation "def s := \"hello\"" "\"hello\"" "false"

-- An interpolated string (`s!"…"`) is split into literal chunks and interpolated terms. Each chunk
-- is a `.str` flagged as an interpolation, and runs from `"`/`}` through the following `{`/`"`
-- (inclusive) — the inner whitespace around `{1}` is the term's trivia, not part of either chunk.
#assertKind "def s := s!\"foo {1} baz\"" "\"foo {" "str"
#assertKind "def s := s!\"foo {1} baz\"" "} baz\"" "str"
#assertStrInterpolation "def s := s!\"foo {1} baz\"" "\"foo {" "true"
#assertStrInterpolation "def s := s!\"foo {1} baz\"" "} baz\"" "true"
-- The interpolated term itself is highlighted normally (here a numeral).
#assertKind "def s := s!\"foo {1} baz\"" "1" "num"
-- An interpolated string with no `{}` is still a single interpolation chunk.
#assertStrInterpolation "def s := s!\"plain\"" "\"plain\"" "true"
-- Round-trips byte-for-byte through the includes-unparsed path.
#evalHighlight' "def s := s!\"foo {1} baz\"" "def s := s!\"foo {1} baz\""

-- Comments are split into delimiter tokens (`--`, `/-`, `-/`) and body text, and the surrounding
-- source still round-trips byte-for-byte. A trailing line comment lives in trailing trivia; a
-- block comment in leading trivia of an inner token. Both paths are exercised.
#assertKind "def x := 1 -- note" "--" "commentDelim"
#assertKind "def x := 1 -- note" " note" "lineComment"
#evalHighlight' "def x := 1 -- note" "def x := 1 -- note"
#assertKind "def y :=\n  /- block -/ 2" "/-" "commentDelim"
#assertKind "def y :=\n  /- block -/ 2" "-/" "commentDelim"
#assertKind "def y :=\n  /- block -/ 2" " block " "blockComment"
#evalHighlight' "def y :=\n  /- block -/ 2" "def y :=\n  /- block -/ 2"
-- Nested block comments are depth-balanced: only the outermost `/-` / `-/` are delimiter tokens,
-- and the nested delimiters remain part of the single body text. Round-trips byte-for-byte.
#assertKind "def z :=\n  /- a /- b -/ c -/ 3" "/-" "commentDelim"
#assertKind "def z :=\n  /- a /- b -/ c -/ 3" "-/" "commentDelim"
#assertKind "def z :=\n  /- a /- b -/ c -/ 3" " a /- b -/ c " "blockComment"
#evalHighlight' "def z :=\n  /- a /- b -/ c -/ 3" "def z :=\n  /- a /- b -/ c -/ 3"
-- Leading comments before the first command are trivia, even though the includes-unparsed path sees
-- them as a source gap from the caller-provided `startPos?` to the first syntax token.
#assertKindRich "-- A line comment\ndef commented : Nat := 42\n/- A block comment -/" "--" "commentDelim"
#assertKindRich "-- A line comment\ndef commented : Nat := 42\n/- A block comment -/" " A line comment" "lineComment"
#assertKindRich "-- A line comment\ndef commented : Nat := 42\n/- A block comment -/" "/-" "commentDelim"
#assertKindRich "-- A line comment\ndef commented : Nat := 42\n/- A block comment -/" " A block comment " "blockComment"
#assertRichNoUnparsed "-- A line comment\ndef commented : Nat := 42\n/- A block comment -/"
-- Diagnostic boundaries may split a trivia-only leading gap; each segment should still be emitted
-- as trivia rather than `.unparsed`.
#assertRichNoUnparsed "-- A line comment\n/- A block comment -/\ndef commented : Nat := 42

def inject (start fin : Nat) (str : String) : Lean.Elab.Command.CommandElabM Unit := do
  let stx := Lean.Syntax.atom (.synthetic ⟨start⟩ ⟨fin⟩) (String.mk [])
  Lean.logInfoAt stx str

elab \"inject_info\" : command => do
  inject 0 17 \"subverso_test: leading line comment\"

inject_info"
-- Non-trivia recovered source remains `.unparsed`; comment tokenization of source gaps is
-- all-or-nothing per message-split segment.
#assertRichHasUnparsed "deriving a bunch of other filler text def b := true" "a bunch of other filler text "
-- If strict trivia production accepts a comment and then later finds non-trivia source in the same
-- gap segment, the speculative comment tokens must be rolled back before the `.unparsed` fallback.
#assertRichHasUnparsed "deriving a -- rollback marker
bunch of other filler text def b := true

def inject (start fin : Nat) (str : String) : Lean.Elab.Command.CommandElabM Unit := do
  let stx := Lean.Syntax.atom (.synthetic ⟨start⟩ ⟨fin⟩) (String.mk [])
  Lean.logInfoAt stx str

elab \"inject_info\" : command => do
  inject 10 11 \"subverso_test: rollback split\"

inject_info" "-- rollback marker\nbunch of other filler text "
#assertRichLacksToken "deriving a -- rollback marker
bunch of other filler text def b := true

def inject (start fin : Nat) (str : String) : Lean.Elab.Command.CommandElabM Unit := do
  let stx := Lean.Syntax.atom (.synthetic ⟨start⟩ ⟨fin⟩) (String.mk [])
  Lean.logInfoAt stx str

elab \"inject_info\" : command => do
  inject 10 11 \"subverso_test: rollback split\"

inject_info" " rollback marker" "lineComment"

-- `-- ANCHOR:` / `-- ANCHOR_END:` directives are still recognized after comment tokenization, and
-- the whole directive line (with its newline) is consumed — no extra blank lines, and the anchor
-- has no stray leading/trailing newline (checked untrimmed).
#assertAnchor "def pre := 0\n-- ANCHOR: foo\ndef x := 1\n-- ANCHOR_END: foo\ndef post := 2" "foo" "def x := 1\n"
-- Indented directive comments are recognized too, and their indentation is consumed with the line;
-- the kept code retains its own indentation.
#assertAnchor "def pre := 0\nsection\n  -- ANCHOR: bar\n  def x := 1\n  -- ANCHOR_END: bar\nend" "bar" "  def x := 1\n"
-- A trailing comment that merely looks like a directive is NOT a directive line (the line doesn't
-- begin with `--`), so it stays a highlighted comment token rather than being flattened to text.
#assertAnchorKeepsComment "def x := 1 -- ANCHOR: note" " ANCHOR: note"

-- Proof-state directives are recognized after comment tokenization (the `commentDelim`/`lineComment`
-- retexting path), with the `^` column resolved against the tactic line above.
#assertProofState "example : True := by\n  trivial\n--^ PROOF_STATE: st" "st"
-- An *indented* proof-state directive inside a tactic block: its indentation must stay attached to
-- the comment (the comment token must not be pulled into the tactic region away from its
-- whitespace), so the `^` column is computed correctly. Checked through the module path (the way
-- `demo-toml/Anchors.lean` is highlighted), which is where this separation actually occurs.
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let hl ← highlightModuleStyle "theorem t : ∀ (n : Nat), n = n := by\n  intro n\n  --^ PROOF_STATE: afterIntro\n  rfl"
  match hl.anchored with
  | .error e => throwError m!"module-style proof-state extraction failed: {e}"
  | .ok ex =>
    unless (Compat.HashMap.get? ex.proofStates "afterIntro").isSome do
      throwError "no proof state 'afterIntro' (module-style highlighting)"

-- The whole `rw [h₁, …, hₙ]` invocation gets the final proof state, and each rewrite rule gets its
-- own intermediate state (after that rewrite) *nested inside* that region. `rewrite` behaves the
-- same. Previously the whole `rw [...]` collapsed to a single, flat final state.
namespace SubVerso.Highlighting
/-- Each `.tactics` region as `(nestingDepth, code, goalConclusions)`, in pre-order. -/
partial def Highlighted.stateTree (hl : Highlighted) (depth : Nat := 0) : Array (Nat × String × List String) := Id.run do
  let mut out := #[]
  match hl with
  | .seq hls => for x in hls do out := out ++ x.stateTree depth
  | .span _ hl' => out := out ++ hl'.stateTree depth
  | .tactics info _ _ hl' =>
    out := out.push (depth, hl'.asString, (info.map (fun g => g.conclusion.asString)).toList)
    out := out ++ hl'.stateTree (depth + 1)
  | _ => pure ()
  out
end SubVerso.Highlighting

-- Some newer tactic syntax — `obtain … : T := by …`, `replace … : T := by …` — doesn't exist on
-- older toolchains.
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let hasObtain :=
    (Parser.runParserCategory env `tactic "obtain x : True := by trivial").isOk
  elabCommand (← `(def$(mkIdent `hasObtain) : Bool := $(quote hasObtain)))

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let hasReplace :=
    (Parser.runParserCategory env `tactic "replace x : True := by trivial").isOk
  elabCommand (← `(def$(mkIdent `hasReplace) : Bool := $(quote hasReplace)))

open Lean Elab Command in
/-- Asserts the nested proof-state tree of `src` (highlighted module-style) equals `expected`. Does
nothing when `skip` is true — used to skip tactics whose syntax doesn't parse on this toolchain. -/
def assertStateTree (src : String) (expected : List (Nat × String × List String))
    (skip : Bool := false) : CommandElabM Unit := do
  if skip then return
  let tree := (← highlightModuleStyle src).stateTree.toList
  unless tree == expected do
    throwError m!"proof-state tree =\n{repr tree}\nexpected\n{repr expected}"

open Lean Elab Command in
/--
Asserts the nested proof-state tree of `src` (highlighted module-style) equals `expected`, after
dropping nested `by`-token regions (those at depth > 0 whose code is `"by"`).

Whether a macro tactic's embedded `by` carries a state is toolchain-dependent: some Lean versions
record it with the subproof's goal (so it is shown), later ones with the *enclosing* goal (so
`Code.conclusionDuplicatesEnclosing` drops it as redundant). That nested-`by` state is therefore not
a guaranteed output, so this asserts only the stable structure — the whole-tactic region and the real
subproof steps.

For tactics whose nested `by` state *is* stable, use `assertStateTree`, which compares exactly.

Does nothing when `skip` is true — used to skip tactics whose syntax doesn't parse on this toolchain.
-/
def assertStateTreeIgnoringNestedBy (src : String) (expected : List (Nat × String × List String))
    (skip : Bool := false) : CommandElabM Unit := do
  if skip then return
  let tree := (← highlightModuleStyle src).stateTree.toList.filter fun (depth, code, _) => !(depth > 0 && code == "by")
  unless tree == expected do
    throwError m!"proof-state tree (ignoring nested `by`) =\n{repr tree}\nexpected\n{repr expected}"

-- `rw`: the closing `rfl` solves the goal, so the outer `rw [...]` region shows the empty (solved)
-- state, with the three rewrite steps nested at depth 1. Each step's region spans the elaborator's
-- recorded node — the rule together with its trailing separator — so the non-final steps include the
-- `,` (the last step has no trailing comma).
open Lean Elab Command in
#eval assertStateTree
  "theorem rwSteps (a b c d : Nat) (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d := by\n  rw [h1, h2, h3]"
  [(0, "by", ["a = d"]),
   (0, "rw [h1, h2, h3]", []),
     (1, "h1,", ["b = d"]), (1, "h2,", ["c = d"]), (1, "h3", ["d = d"])]

-- `rewrite` behaves identically: the outer region shows the final state after both rewrites, with
-- each step nested. (Here `rfl` is a separate following tactic.)
open Lean Elab Command in
#eval assertStateTree
  "theorem rwLike (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by\n  rewrite [h1, h2]\n  rfl"
  [(0, "by", ["a = c"]),
   (0, "rewrite [h1, h2]", ["c = c"]),
     (1, "h1,", ["b = c"]), (1, "h2", ["c = c"]),
   (0, "rfl", [])]

-- A multi-binder `intro h1 h2 h3` is one tactic, so it gets a single region showing the state *after*
-- all the intros — `a = d` — rather than the state landing only on the last binder (`h3`). Like
-- `simp`, the whole tactic wins over its more-specific sub-states. (Regression guard: previously the
-- whole-`intro` region was dropped by the "most specific span" filter, leaving the state on `h3`.)
open Lean Elab Command in
#eval assertStateTree
  "example (a b c d : Nat) : a = b → b = c → c = d → a = d := by\n  intro h1 h2 h3\n  rw [h1, h2, h3]"
  [(0, "by", ["a = b → b = c → c = d → a = d"]),
   (0, "intro h1 h2 h3", ["a = d"]),
   (0, "rw [h1, h2, h3]", []),
     (1, "h1,", ["b = d"]), (1, "h2,", ["c = d"]), (1, "h3", ["d = d"])]

-- `replace h : T := by …` is `have`'s sibling (it rebinds `h`): same macro shape, so the whole
-- `replace` shows the state after it, with the subproof's real steps nested inside. (Asserted modulo
-- the nested `by` token, which is toolchain-dependent — see the `have` tests below.)
open Lean Elab Command in
#eval assertStateTreeIgnoringNestedBy
  "example (h : Nat) : True := by\n  replace h : Int := by exact 0\n  trivial"
  [(0, "by", ["True"]),
   (0, "replace h : Int := by exact 0", ["True"]),
     (1, "exact 0", []),
   (0, "trivial", [])]
  (skip := !hasReplace)

-- `suffices h : T by …` is one tactic: the whole `suffices` shows the state *after* it — the new
-- (sufficient) goal `T` — and the nested `by …` (which discharges the *original* goal from `h`) keeps
-- its own state, since it differs from the `suffices` region's conclusion and isn't shadowed by an
-- open enclosing region of the same conclusion.
open Lean Elab Command in
#eval assertStateTree
  "example : True := by\n  suffices h : Nat by trivial\n  exact 0"
  [(0, "by", ["True"]),
   (0, "suffices h : Nat by trivial", ["Nat"]),
     (1, "by", ["True"]),
     (1, "trivial", []),
   (0, "exact 0", [])]

-- `let … := by …`, like `have`, is one tactic, so the whole `let` shows the state *after* it (the
-- goal with `x` bound). Unlike `have`, `let`'s embedded `by` is *not* macro-mangled — its tacticSeq
-- is recorded with the subproof's own goal — so the nested `by` keeps its (correct) state, since it
-- differs from the enclosing conclusion and `conclusionsDuplicateOpen` leaves it alone.
open Lean Elab Command in
#eval assertStateTree
  "example : True := by\n  let x : Nat := by exact 0\n  trivial"
  [(0, "by", ["True"]),
   (0, "let x : Nat := by exact 0", ["True"]),
     (1, "by", ["Nat"]),
     (1, "exact 0", []),
   (0, "trivial", [])]
open Lean Elab Command in
#eval assertStateTree
  "example : True := by\n  let x : Nat × Nat := by\n    refine ⟨?_, ?_⟩\n    · exact 0\n    · exact 1\n  trivial"
  [(0, "by", ["True"]),
   (0, "let x : Nat × Nat := by\n    refine ⟨?_, ?_⟩\n    · exact 0\n    · exact 1", ["True"]),
     (1, "by", ["Nat × Nat"]),
     (1, "refine ⟨?_, ?_⟩", ["Nat", "Nat"]),
     (1, "·", ["Nat"]), (1, "exact 0", []),
     (1, "·", ["Nat"]), (1, "exact 1", []),
   (0, "trivial", [])]

-- `have … := by …` is a single tactic, so the whole `have` gets a region showing the state *after*
-- it (the goal with `h` added), with the subproof's steps nested inside at depth 1. (Asserted modulo
-- the nested `by` token: `have` is a macro, and whether its embedded `by` carries a state varies by
-- toolchain.)
open Lean Elab Command in
#eval assertStateTreeIgnoringNestedBy
  "example : True := by\n  have h : 2 = 2 := by rfl\n  trivial"
  [(0, "by", ["True"]),
   (0, "have h : 2 = 2 := by rfl", ["True"]),
     (1, "rfl", []),
   (0, "trivial", [])]
-- A multi-step subproof keeps every nested step.
open Lean Elab Command in
#eval assertStateTreeIgnoringNestedBy
  "example : True := by\n  have h : 1 = 1 ∧ 2 = 2 := by\n    constructor\n    · rfl\n    · rfl\n  trivial"
  [(0, "by", ["True"]),
   (0, "have h : 1 = 1 ∧ 2 = 2 := by\n    constructor\n    · rfl\n    · rfl", ["True"]),
     (1, "constructor", ["1 = 1", "2 = 2"]),
     (1, "·", ["1 = 1"]), (1, "rfl", []),
     (1, "·", ["2 = 2"]), (1, "rfl", []),
   (0, "trivial", [])]

-- An `obtain` that discharges its goal with a nested `by` is a single tactic, so the whole
-- `obtain … := …` gets a region showing the state *after* the destructuring, with the nested `by`
-- proof's states nested inside at depth 1 (like `rw`). (Regression guard: previously the whole
-- `obtain` region was dropped because `childHasTactics` counted the nested `by`'s tactic info,
-- leaving only the flat nested `by` states and no clickable `obtain` region.) Both the `:= by …`
-- form and the `:= f … (by …)` argument form are covered.
open Lean Elab Command in
#eval assertStateTree
  "example : True := by\n  obtain ⟨k, hk⟩ : ∃ k : Nat, k = 0 := by exact ⟨0, rfl⟩\n  trivial"
  [(0, "by", ["True"]),
   (0, "obtain ⟨k, hk⟩ : ∃ k : Nat, k = 0 := by exact ⟨0, rfl⟩", ["True"]),
     (1, "by", ["∃ k, k = 0"]),
     (1, "exact ⟨0, rfl⟩", []),
   (0, "trivial", [])]
  (skip := !hasObtain)
open Lean Elab Command in
#eval assertStateTree
  "example : True := by\n  obtain ⟨k, hk⟩ := id (α := ∃ k : Nat, k = 0) (by exact ⟨0, rfl⟩)\n  trivial"
  [(0, "by", ["True"]),
   (0, "obtain ⟨k, hk⟩ := id (α := ∃ k : Nat, k = 0) (by exact ⟨0, rfl⟩)", ["True"]),
     (1, "by", ["∃ k, k = 0"]),
     (1, "exact ⟨0, rfl⟩", []),
   (0, "trivial", [])]
  (skip := !hasObtain)

-- Comments that look like directives but are not directive *lines* must keep their token styling:
-- a block comment and an ordinary full-line comment, both containing `ANCHOR:`.
#assertAnchorCodeHasToken "def x := 1\n/- ANCHOR: foo -/\ndef y := 2" "blockComment" " ANCHOR: foo "
#assertAnchorKeepsComment "def x := 1\n-- not ANCHOR: foo\ndef y := 2" " not ANCHOR: foo"

-- Disabling a flag leaves the corresponding directive comments untouched in the extracted code.
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let hl ← highlightFromString "def a := 0\n-- ANCHOR: foo\ndef x := 1\n-- ANCHOR_END: foo"
  match hl.anchored (textAnchors := false) with
  | .error e => throwError m!"unexpected error with textAnchors := false: {e}"
  | .ok ex =>
    unless ex.code.tokenList.any (fun t => t.kind.name == "lineComment" && t.content == " ANCHOR: foo") do
      throwError "ANCHOR comment was not preserved with textAnchors := false"
    unless ex.anchors.isEmpty do throwError "anchors found despite textAnchors := false"

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let hl ← highlightWithPrefixedMessages "example : True := by\n  trivial\n--^ PROOF_STATE: st"
  match hl.anchored (proofStates := false) with
  | .error e => throwError m!"unexpected error with proofStates := false: {e}"
  | .ok ex =>
    unless ex.code.tokenList.any (fun t => t.kind.name == "lineComment" && t.content == "^ PROOF_STATE: st") do
      throwError "PROOF_STATE comment was not preserved with proofStates := false"

-- Error cases still fire after comment tokenization.
#assertAnchorError "def x := 1\n-- ANCHOR_END: foo\ndef y := 2" "Anchor not open"
#assertAnchorError "def a := 0\n-- ANCHOR: foo\ndef x := 1\n-- ANCHOR: foo\ndef y := 2" "Anchor already opened"
#assertAnchorError "def a := 0\n-- ANCHOR: foo\ndef x := 1" "Unclosed anchors"

-- Duplicate proof-state name (needs tactic info, so via the info-recording harness).
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let hl ← highlightWithPrefixedMessages "example : True := by\n  trivial\n--^ PROOF_STATE: st\n--^ PROOF_STATE: st"
  match hl.anchored with
  | .ok _ => throwError "expected a duplicate proof-state error"
  | .error e =>
    unless "Proof state already found".isPrefixOf e do throwError m!"unexpected error: {e}"

-- A directive comment inside a tactic block is extracted with its surrounding tactic context
-- (exercises the `ctx` threading in `anchored`).
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let hl ← highlightWithPrefixedMessages "example : True := by\n  -- ANCHOR: pf\n  trivial\n  -- ANCHOR_END: pf"
  match hl.anchored with
  | .error e => throwError m!"anchored failed: {e}"
  | .ok ex =>
    match Compat.HashMap.get? ex.anchors "pf" with
    | none => throwError "no anchor 'pf'"
    | some a =>
      unless (a.toString.splitOn "trivial").length > 1 do
        throwError m!"anchor 'pf' lost its tactic content: {repr a.toString}"
      -- The `.tactics` wrapper must survive extraction, not just the text content.
      unless a.hasTactics do
        throwError m!"anchor 'pf' lost its tactic-state wrapper: {repr a}"

-- Exact newline/indentation behavior: a directive at end-of-input (no trailing newline), blank lines
-- around a directive, and a tab-indented directive (tabs count as line-leading whitespace).
#assertAnchor "def a := 0\n-- ANCHOR: foo\ndef x := 1\n-- ANCHOR_END: foo" "foo" "def x := 1\n"
#assertAnchor "def a := 0\n\n-- ANCHOR: foo\n\ndef x := 1\n-- ANCHOR_END: foo" "foo" "\ndef x := 1\n"
-- A more deeply indented directive (extra leading spaces) is still recognized as a line start.
#assertAnchor "def a := 0\nsection\n    -- ANCHOR: foo\n    def x := 1\n    -- ANCHOR_END: foo\nend" "foo" "    def x := 1\n"

-- Operators are `.operator`, including multi-character symbols (classified per character) and
-- Unicode math symbols like the function arrow.
#assertKind "def f (a b : Nat) := a + b" "+" "operator"
#assertKind "def g (a : Option Nat) (b : Nat → Option Nat) := a >>= b" ">>=" "operator"
#assertKind "def fn : Nat → Nat := id" "→" "operator"
-- A subscript/superscript-decorated operator (an operator char plus subscript/superscript chars)
-- is still an operator, including superscript operator signs like `⁻` in `⁻¹`.
#assertKind "infixl:65 \" +ₙ \" => Nat.add\ndef z := 1 +ₙ 2" "+ₙ" "operator"
-- A superscript-minus operator char plus a superscript digit classifies as an operator. Uses the
-- obscure `⁻²` token rather than `⁻¹`, which would clash with the built-in `Inv.inv` notation.
#assertKind "postfix:max \"⁻²\" => Nat.succ\ndef w := 0⁻²" "⁻²" "operator"
-- But a letter-like notation symbol that doesn't resolve stays `.unknown` rather than being
-- mislabeled as an operator (it has no operator character).
#assertKind "prefix:max \"𝒫\" => Nat.succ\ndef y := 𝒫 0" "𝒫" "unknown"

-- List brackets and separators
#assertKind "def l := [1, 2]" "[" "bracket"
#assertKind "def l := [1, 2]" "]" "bracket"
#assertKind "def l := [1, 2]" "," "separator"
-- The array-literal opener `#[` is a single token combining `#` with `[`; it is a bracket too.
#assertKind "def arr := #[1, 2]" "#[" "bracket"
#assertKind "def arr := #[1, 2]" "]" "bracket"
-- A letter-prefixed bracket notation (`foo[ … ]`) is bracket-like, not a keyword.
#assertKind "notation:max \"foo[\" n \"]\" => n\ndef z := foo[5]" "foo[" "bracket"
-- A mathematical-script-letter prefix (`ℰ⟦ … ⟧`) counts as a letter, so this is a bracket too.
#assertKind "notation:max \"ℰ⟦\" n \"⟧\" => n\ndef z := ℰ⟦5⟧" "ℰ⟦" "bracket"
#assertKind "notation \"{!\" n \"!}\" => n\ndef w := {! 5 !}" "{!" "bracket"
#assertKind "notation \"{!\" n \"!}\" => n\ndef w := {! 5 !}" "!}" "bracket"
-- The separator sits inside a `sepBy` null grouping; it must inherit the surrounding list
-- production rather than the meaningless `null` kind.
#assertOccurrenceNotNull "def l := [1, 2]" ","

-- Anonymous-constructor delimiters keep `.anonCtor` (carrying the constructor's name/signature),
-- rather than being reclassified as brackets/separators by the new lexical step. Verified through
-- the info-recording highlight path, where the applied constructor `Prod.mk 1 2` is resolved.
#assertKindRich "def p : Nat × Nat := ⟨1, 2⟩" "⟨" "anonCtor"
#assertKindRich "def p : Nat × Nat := ⟨1, 2⟩" "⟩" "anonCtor"
#assertKindRich "def p : Nat × Nat := ⟨1, 2⟩" "," "anonCtor"

-- Core symbolic delimiters (`:=`, `=>`, …) are `.delim`, not `.operator` and not the bold `.keyword`
#assertKind "def x := 1" ":=" "delim"
#assertKind "def f := fun (x : Nat) => x" "=>" "delim"
-- A run of only `.` is a delimiter (e.g. the projection dot).
#assertKindRich "def n : Nat := (0 : Nat).succ" "." "delim"
-- A `·` proof-focus bullet has no term info, so it is a delimiter; an anonymous-function
-- placeholder `(· + 1)` resolves to a variable and keeps that kind.
#assertKindRich "example : True ∧ True := by\n  refine ⟨?_, ?_⟩\n  · trivial\n  · trivial" "·" "delim"
#assertKindRich "def f : Nat → Nat := (· + 1)" "·" "var"
-- An anonymous `instance` keyword resolves span-exact to the synthesized instance name, but must
-- stay a keyword rather than being rendered as that constant.
#assertKindRich "class Foo (α : Type) where\n  bar : α\ninstance : Foo Nat where\n  bar := 0" "instance" "keyword"

-- A wildcard / hole `_` is its own kind, not a `.var` (so it isn't italicized like a variable)
#assertKind "def f := fun (_ : Nat) => 0" "_" "wildcard"
#assertKindRich "def f := fun (_ : String) => 0" "_" "wildcard"
#assertKindRich "def f (n : Nat) := match n with\n  | _ => 0" "_" "wildcard"
-- Like `var`, a wildcard keeps the inferred type of its binder for hover.
#assertWildcardType "def f := fun (_ : Nat) => 0" "_" "Nat"

-- Module docs are tagged like doc comments
#assertHasKind "/-! module doc -/" "docComment"

-- The derived `ToJson`/`FromJson` instances round-trip every new token kind
#evalString "true\n"
  (([Token.Kind.num (some "Nat") none, .num none none, .char 'a', .lineComment, .blockComment,
     .commentDelim, .operator (some `foo) (some "foo-1") (some "d"), .bracket none none none,
     .separator none none none, .delim (some `foo) (some "foo-1") (some "d"),
     .wildcard "Nat" none, .wildcard "" (some "[]"), .str (some "x") false, .str none true]
     : List Token.Kind).all (fun k => Token.jsonRoundtrips ⟨k, "x"⟩))

-- The new `identKind`-first atom step: a nullary notation atom (`ℕ`) resolves span-exact to its
-- constant (`.const`), while a genuine infix operator (`+`) has no span-exact info and stays
-- `.operator`. Both require the info-recording highlight path (`#assertKindRich`), as in real
-- extraction; this needs no Mathlib — a local `notation` suffices.
#assertKindRich "notation \"ℕ\" => Nat\ndef m : ℕ := 0" "ℕ" "const"
#assertKindRich "def f (a b : Nat) := a + b" "+" "operator"

-- Checks that we correctly register projection function info for fields/methods
#assertKindRich "structure S where\n  x : Nat" "x" "const"
#assertKindRich "class C (a : Type) where\n  f : a → a" "f" "const"

-- Declaration ranges are registered as a command ends, so definition sites must be recognized in
-- the command's final environment.
#assertDefines "def foo := 1" "foo"
#assertDefines "theorem bar : True := trivial" "bar"
#assertDefines "structure S where\n  x : Nat" "S"
#assertDefines "inductive T where\n  | a\n  | b" "T" "T.a" "T.b"

-- Local definitions from `let rec` and `where` blocks are marked as definition sites from Lean 4.7
-- on. Their enclosing top-level definitions are marked on every toolchain.
def localDefinitionSites : Bool :=
  Lean.version.major > 4 || (Lean.version.major == 4 && Lean.version.minor >= 7)

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let locals (names : List Name) : List Name := if localDefinitionSites then names else []
  assertDefines "def f := helper\nwhere helper := 1" ([`f] ++ locals [`f.helper])
  assertDefines (String.intercalate "\n" [
      "def one (n : Nat) : Nat :=",
      "  let rec loop : Nat → Nat",
      "    | 0 => 0",
      "    | k + 1 => loop k",
      "  loop n",
      "def two (n : Nat) : Nat := helper n",
      "where helper (k : Nat) : Nat := k + 1",
      "def three (n : Nat) : Nat :=",
      "  let rec up (k : Nat) : Nat := k + 1",
      "  let rec down (k : Nat) : Nat := k - 1",
      "  up (down n)",
      "def four (n : Nat) : Nat := aux n + other n",
      "where",
      "  aux (k : Nat) : Nat := k",
      "  other (k : Nat) : Nat := k * 2"])
    ([`one, `two, `three, `four] ++
      locals [`one.loop, `two.helper, `three.up, `three.down, `four.aux, `four.other])

-- `:=` stays a `.delim` across contexts even on the info-recording path, where `identKind` could
-- otherwise match its span: a structure-instance field, an `instance … where` field, and a tactic
-- `have` all keep it a delim (it is peeled off before `identKind` is consulted).
#assertKindRich "structure S where\n  x : Nat\n#check ({ x := 1 } : S)" ":=" "delim"
#assertKindRich "class C (a : Type) where\n  f : a → a\ninstance : C Nat where\n  f x := x" ":=" "delim"
#assertKindRich "theorem t : True := by\n  have h : True := trivial\n  exact h" ":=" "delim"

end TokenKinds

section TermMatching

-- `dropPrefix?` compares the characters of the prefix, not just its length
#evalString "true\n" (("hello world".dropPrefix? "hello ").map (·.toString) == some "world")
#evalString "true\n" ("hello world".dropPrefix? "hallo ").isNone
#evalString "true\n" ("hi".dropPrefix? "hello ").isNone

/--
`#evalMatchingExpr inp term exp` highlights `inp`, looks up `term` with `matchingExpr?`, and checks
that the matched code renders as `exp`.
-/
elab "#evalMatchingExpr" inp:str term:str exp:str : command => do
  let hl ← highlightWithPrefixedMessages inp.getString
  let some found := hl.matchingExpr? term.getString
    | throwErrorAt term m!"No match for {String.quote term.getString} in\n{inp.getString}"
  if found.asString != exp.getString then
    throwError m!"Mismatched match\n---Found:---\n{found.asString}\n\n---Expected:---\n{exp.getString}"

/--
`#evalNoMatchingExpr inp term` highlights `inp` and checks that `matchingExpr?` finds no match for
`term`.
-/
elab "#evalNoMatchingExpr" inp:str term:str : command => do
  let hl ← highlightWithPrefixedMessages inp.getString
  if let some found := hl.matchingExpr? term.getString then
    throwErrorAt term m!"Expected no match for {String.quote term.getString}, got\n{found.asString}"

-- A term is matched across the comments that separate its tokens, and the match renders with
-- whitespace from the search string rather than the comment.
#evalMatchingExpr
  "def f (b : Bool) : Option Nat :=\n  if b then\n    some 0\n  else -- nothing to report\n    none"
  "else none" "else none"

#evalMatchingExpr
  "def f (b : Bool) : Option Nat :=\n  if b then some 0 else /- nothing to report -/ none"
  "else none" "else none"

-- Matching starts at the token after a leading comment.
#evalMatchingExpr "-- a leading comment\ndef x := 1 + 2" "1 + 2" "1 + 2"

-- Comment content is not itself matchable as a term.
#evalNoMatchingExpr "def x := 1 -- plus 2\n" "plus 2"

end TermMatching

/-! # Async Elaboration -/
section AsyncElab
open SubVerso.Highlighting

open Lean Elab Command in
-- Under async elaboration, a `match`-using definition's auxiliary declarations get the names the
-- compiler gives them, so a reference to such a name (as shown in the editor) elaborates cleanly.
-- The generated names gained an extra suffix in the 4.21 cycle.
#eval show CommandElabM Unit from do
  if Compat.Frontend.asyncSupport?.isSome then
    let auxName :=
      if Lean.version.major > 4 || (Lean.version.major == 4 && Lean.version.minor >= 21) then
        "mySubst.match_1_1"
      else
        "mySubst.match_1"
    let hl ← highlightModuleStyle
      s!"theorem mySubst \{p : Nat → Prop} : x = y → p x → p y\n  | rfl, h => h\n\n#check @{auxName}\n"
    if hl.hasError then
      throwError m!"Unexpected error:\n{hlStringWithMessages hl}"

open Lean Elab Command in
-- Tactic proof states survive async elaboration: the info trees' lazy holes are resolved before
-- highlighting.
#eval show CommandElabM Unit from do
  if Compat.Frontend.asyncSupport?.isSome then
    let hl ← highlightModuleStyle "example : 2 + 2 = 4 := by\n  rfl\n"
    unless hl.hasTactics do
      throwError "No proof states found under async elaboration"

end AsyncElab

/-!
# Splitting and substitution preserve nesting

`Highlighted.split` and `Highlighted.substM` walk into `span` and `tactics` wrappers. Each
fragment is wrapped in the wrappers that enclose it, and each of those wrappers occurs exactly
once in the fragment.
-/

section SplitNesting

open SubVerso.Highlighting

private def tokA : Highlighted := .token ⟨.keyword none none none, "a"⟩
private def tokB : Highlighted := .token ⟨.keyword none none none, "b"⟩
private def tokC : Highlighted := .token ⟨.keyword none none none, "c"⟩

private def msg (k : Highlighted.Span.Kind) (s : String) :
    Highlighted.Span.Kind × Highlighted.MessageContents Highlighted :=
  (k, .text s)

private def nested : Highlighted :=
  .span #[msg .info "outer"] (.seq #[tokA, .span #[msg .warning "inner"] tokB, tokC])

private def nested3 : Highlighted :=
  .span #[msg .info "o"] (.span #[msg .warning "m"] (.span #[msg .info "i"] tokB))

/-- The number of span wrappers in the tree. -/
private partial def countSpans : Highlighted → Nat
  | .seq xs => xs.foldl (fun n x => n + countSpans x) 0
  | .span _ c => 1 + countSpans c
  | .tactics _ _ _ c => countSpans c
  | _ => 0

/-- The number of tactic-state wrappers in the tree. -/
private def countTactics (hl : Highlighted) : Nat := hl.stateTree.size

/-- The highlighted parts of a substitution, with the substituted values discarded. -/
private def substParts (values : String → Option Unit) (hl : Highlighted) : Array Highlighted :=
  hl.subst values |>.filterMap fun p =>
    match p with
    | .inl h => some h
    | .inr () => none

private def noMatch : String → Option Unit := fun _ => none

private def substSpans (hl : Highlighted) : Nat :=
  substParts noMatch hl |>.foldl (fun n h => n + countSpans h) 0

private def substString (hl : Highlighted) : String :=
  substParts noMatch hl |>.foldl (fun s h => s ++ h.asString) ""

-- Substitution without matches keeps each span exactly once, and all the content.
#evalString "2\n" (substSpans nested)
#evalString "\"abc\"\n" (substString nested)
#evalString "3\n" (substSpans nested3)
#evalString "\"b\"\n" (substString nested3)

-- A substitution match outside the spans does not affect them.
#evalString "3\n" ((substParts (fun s => if s == "a" then some () else none)
    (.seq #[tokA, nested3, tokC])).foldl (fun n h => n + countSpans h) 0)

-- Splitting without matches keeps each span exactly once.
#evalString "2\n" ((nested.split (fun _ => false)).foldl (fun n h => n + countSpans h) 0)
#evalString "3\n" ((nested3.split (fun _ => false)).foldl (fun n h => n + countSpans h) 0)

private def nestedTactics : Highlighted :=
  .tactics #[] 0 0 (.seq #[tokA, .tactics #[] 0 0 tokB, tokC])

-- Tactic-state wrappers behave like spans when there is nothing to split on.
#evalString "2\n" ((nestedTactics.split (fun _ => false)).foldl (fun n h => n + countTactics h) 0)
#evalString "2\n" ((substParts noMatch nestedTactics).foldl (fun n h => n + countTactics h) 0)
#evalString "\"abc\"\n" ((substParts noMatch nestedTactics).foldl (fun s h => s ++ h.asString) "")

-- `lines` repeats a wrapper on each line of its content, and only there.
#evalString "2\n" ((Highlighted.span #[msg .info "o"] (.text "x\ny")).lines.foldl
  (fun n h => n + countSpans h) 0)

private def mark : Highlighted := .token ⟨.keyword none none none, "MARK"⟩

private def atMark (s : String) : Bool := s == "MARK"

private def atMark? (s : String) : Option Unit := if s == "MARK" then some () else none

/-- A marker in the outer wrapper, reached after the inner wrapper has closed. -/
private def markAfterInner : Highlighted :=
  .span #[msg .info "outer"] (.seq #[.span #[msg .warning "inner"] tokA, mark, tokB])

/-- A marker in the inner wrapper, with content before the inner wrapper opened. -/
private def markInsideInner : Highlighted :=
  .span #[msg .info "outer"]
    (.seq #[tokA, .span #[msg .warning "inner"] (.seq #[tokB, mark, tokC])])

/-- `markAfterInner` with tactic states in place of spans. -/
private def tacticsMarkAfterInner : Highlighted :=
  .tactics #[] 0 0 (.seq #[.tactics #[] 0 0 tokA, mark, tokB])

-- Each fragment carries every wrapper that encloses it in the source.
#evalString "#[2, 1]\n" ((markAfterInner.split atMark).map countSpans)
#evalString "#[2, 1]\n" ((substParts atMark? markAfterInner).map countSpans)
#evalString "#[2, 1]\n" ((tacticsMarkAfterInner.split atMark).map countTactics)
#evalString "#[2, 2]\n" ((markInsideInner.split atMark).map countSpans)
#evalString "#[2, 2]\n" ((substParts atMark? markInsideInner).map countSpans)

-- The fragments partition the content in source order.
#evalString "#[\"a\", \"b\"]\n" ((markAfterInner.split atMark).map (·.asString))
#evalString "#[\"ab\", \"c\"]\n" ((markInsideInner.split atMark).map (·.asString))
#evalString "#[\"ab\", \"c\"]\n" ((substParts atMark? markInsideInner).map (·.asString))

/-- A marker as the only content of a wrapper. -/
private def markAlone : Highlighted :=
  .span #[msg .info "outer"] mark

/-- A marker as the first content of a wrapper. -/
private def markAtStart : Highlighted :=
  .span #[msg .info "outer"] (.seq #[mark, tokA])

/-- A marker as the last content of a wrapper. -/
private def markAtEnd : Highlighted :=
  .span #[msg .info "outer"] (.seq #[tokA, mark])

/-- A marker as the first content of the inner wrapper. -/
private def markAtInnerStart : Highlighted :=
  .span #[msg .info "outer"]
    (.seq #[tokA, .span #[msg .warning "inner"] (.seq #[mark, tokB])])

/-- A marker as the last content of the inner wrapper. -/
private def markAtInnerEnd : Highlighted :=
  .span #[msg .info "outer"]
    (.seq #[.span #[msg .warning "inner"] (.seq #[tokA, mark]), tokB])

/-- `markAtEnd` with a tactic state in place of the span. -/
private def tacticsMarkAtEnd : Highlighted :=
  .tactics #[] 0 0 (.seq #[tokA, mark])

-- A wrapper left with no content carries no messages or proof states.
#evalString "#[0, 0]\n" ((markAlone.split atMark).map countSpans)
#evalString "#[0, 1]\n" ((markAtStart.split atMark).map countSpans)
#evalString "#[1, 0]\n" ((markAtEnd.split atMark).map countSpans)
#evalString "#[1, 0]\n" ((tacticsMarkAtEnd.split atMark).map countTactics)
#evalString "#[1, 2]\n" ((markAtInnerStart.split atMark).map countSpans)
#evalString "#[2, 1]\n" ((markAtInnerEnd.split atMark).map countSpans)
#evalString "#[0, 1]\n" ((substParts atMark? markAtStart).map countSpans)
#evalString "#[1, 0]\n" ((substParts atMark? markAtEnd).map countSpans)

#evalString "#[\"\", \"\"]\n" ((markAlone.split atMark).map (·.asString))
#evalString "#[\"\", \"a\"]\n" ((markAtStart.split atMark).map (·.asString))
#evalString "#[\"a\", \"\"]\n" ((markAtEnd.split atMark).map (·.asString))
#evalString "#[\"a\", \"b\"]\n" ((markAtInnerStart.split atMark).map (·.asString))
#evalString "#[\"a\", \"b\"]\n" ((markAtInnerEnd.split atMark).map (·.asString))

/-- A marker with content on either side of it inside one wrapper. -/
private def markInMiddle : Highlighted :=
  .span #[msg .info "outer"] (.seq #[tokA, mark, tokB])

/-- `markInMiddle` with a tactic state in place of the span. -/
private def tacticsMarkInMiddle : Highlighted :=
  .tactics #[] 0 0 (.seq #[tokA, mark, tokB])

private def rejoin (parts : Array Highlighted) : Highlighted :=
  parts.foldl (· ++ ·) .empty

-- Rejoining the fragments recovers the wrappers and the content of the original.
#evalString "1\n" (countSpans (rejoin (markInMiddle.split atMark)))
#evalString "\"ab\"\n" ((rejoin (markInMiddle.split atMark)).asString)
#evalString "1\n" (countTactics (rejoin (tacticsMarkInMiddle.split atMark)))
#evalString "1\n" (countSpans (rejoin (substParts atMark? markInMiddle)))
#evalString "2\n" (countSpans (rejoin (markInsideInner.split atMark)))

end SplitNesting

/-!
# Messages that overlap tactic regions

Messages nest around and interleave with tactic regions. Both kinds of region close in nesting
order: a message that covers a whole proof contains the message regions logged inside it, and a
region that reaches its end while another is still open inside it stays open until the inner one
closes, so it extends to the inner region's end.
-/

section MessageTacticNesting

open SubVerso.Highlighting

open Lean Elab Tactic in
/-- Runs a tactic sequence, first logging an informational note that covers all of it. -/
elab "with_note " ts:Lean.Parser.Tactic.tacticSeq : tactic => do
  logInfo "Noted"
  evalTactic ts

open Lean Elab Tactic in
/-- Runs a tactic, first logging a warning that covers it. -/
elab "flag_tac " t:tactic : tactic => do
  logWarningAt t "Flagged"
  evalTactic t

open Lean Elab Tactic in
/--
Logs a warning that covers the source from `start` to `stop`, then runs `t1` followed by `t2`. The
warning's range is chosen by the caller so that it partially overlaps one tactic's region.
-/
def overlappingWarning (start stop : Option Compat.String.Pos) (t1 t2 : TSyntax `tactic) :
    TacticM Unit := do
  let some start := start | throwError m!"No start position in {t1}"
  let some stop := stop | throwError m!"No end position in {t2}"
  logWarningAt (Syntax.node (.synthetic start stop) nullKind #[]) "Partially covered"
  evalTactic t1
  evalTactic t2

open Lean Elab Tactic in
/--
Runs two tactics, first logging a warning whose range starts at the first tactic and ends
partway into the second, producing a message region that overlaps the second tactic's region.
-/
elab "overlap_note " t1:tactic " overlapping " t2:tactic : tactic =>
  -- The warning ends at the head of `t2` (the `exact` of `exact rfl`), inside `t2`'s region
  overlappingWarning t1.raw.getPos? t2.raw[0].getTailPos? t1 t2

open Lean Elab Tactic in
/--
Runs two tactics, first logging a warning whose range starts partway into the first tactic
and ends at the second tactic's end, producing a message region that overlaps the first
tactic's region.
-/
elab "overlap_note' " t1:tactic " overlapping " t2:tactic : tactic =>
  -- The warning starts at the argument of `t1` (the `rfl` of `exact rfl`), inside `t1`'s region
  overlappingWarning t1.raw[1].getPos? t2.raw.getTailPos? t1 t2

open Lean Elab Tactic in
/--
Runs two tactics, first logging a warning that reaches partway into the second tactic and a note
that starts there, so that the two message ranges overlap each other as well as the second
tactic's region.
-/
elab "crossed_notes " t1:tactic " with " t2:tactic : tactic => do
  let some start := t1.raw.getPos? | throwError m!"No start position in {t1}"
  let some noteStart := t2.raw.getPos? | throwError m!"No start position in {t2}"
  -- The warning ends at the head of `t2` (the `exact` of `exact rfl`), inside `t2`'s region
  let some warnStop := t2.raw[0].getTailPos? | throwError m!"No end position in {t2}"
  let some stop := t2.raw.getTailPos? | throwError m!"No end position in {t2}"
  logWarningAt (Syntax.node (.synthetic start warnStop) nullKind #[]) "Warned"
  logInfoAt (Syntax.node (.synthetic noteStart stop) nullKind #[]) "Noted"
  evalTactic t1
  evalTactic t2

/-- Whether the tree contains a span with a message of the given kind. -/
partial def hasSpanKind (k : Highlighted.Span.Kind) : Highlighted → Bool
  | .seq xs => xs.any (hasSpanKind k)
  | .span infos content => infos.any (·.1 == k) || hasSpanKind k content
  | .tactics _ _ _ content => hasSpanKind k content
  | _ => false

/-- Whether the tree contains a span of kind `outer` with a span of kind `inner` inside it. -/
partial def hasNestedSpans (outer inner : Highlighted.Span.Kind) : Highlighted → Bool
  | .seq xs => xs.any (hasNestedSpans outer inner)
  | .span infos content =>
    (infos.any (·.1 == outer) && hasSpanKind inner content) || hasNestedSpans outer inner content
  | .tactics _ _ _ content => hasNestedSpans outer inner content
  | _ => false

/-- Whether the tree contains a proof state region. -/
partial def hasTacticsNode : Highlighted → Bool
  | .seq xs => xs.any hasTacticsNode
  | .span _ content => hasTacticsNode content
  | .tactics .. => true
  | _ => false

/-- Whether the tree contains a span of kind `k` with a proof state region inside it. -/
partial def hasSpanWithTactics (k : Highlighted.Span.Kind) : Highlighted → Bool
  | .seq xs => xs.any (hasSpanWithTactics k)
  | .span infos content =>
    (infos.any (·.1 == k) && hasTacticsNode content) || hasSpanWithTactics k content
  | .tactics _ _ _ content => hasSpanWithTactics k content
  | _ => false

/-- The code covered by each span with a message of kind `k`, outermost first. -/
partial def spanTexts (k : Highlighted.Span.Kind) : Highlighted → List String
  | .seq xs => Compat.List.flatMap xs.toList (spanTexts k)
  | .span infos content =>
    (if infos.any (·.1 == k) then [content.asString] else []) ++ spanTexts k content
  | .tactics _ _ _ content => spanTexts k content
  | _ => []

open Lean Elab Command in
/-- Checks that `hl` reproduces `input`. -/
def checkRoundTrip (input : String) (hl : Highlighted) : CommandElabM Unit := do
  unless hl.asString == input do
    throwError s!"Expected the highlighted code to round-trip, got: {hl.asString}"

open Lean Elab Command in
-- A message that covers a whole proof contains the message regions logged inside it.
#eval show CommandElabM Unit from do
  let input := String.intercalate "\n" [
    "theorem nestedMessages (n : Nat) : n + 0 = n := by",
    "  with_note",
    "    induction n with",
    "    | zero => flag_tac rfl",
    "    | succ k ih => rfl",
    ""]
  let hl ← highlightModuleStyle input
  unless hasNestedSpans .info .warning hl do
    throwError m!"Expected a warning span nested in an info span:\n{hlStringWithMessages hl}"
  checkRoundTrip input hl

open Lean Elab Command in
-- A message that ends partway into a tactic region stays open until the region closes.
#eval show CommandElabM Unit from do
  let input := String.intercalate "\n" [
    "theorem overlappedRegion : 1 + 1 = 2 := by",
    "  overlap_note skip overlapping exact rfl",
    ""]
  let hl ← highlightModuleStyle input
  let regions := hl.proofStates.toList.map (·.fst)
  unless regions.contains "exact rfl" && regions.contains "skip" do
    throwError s!"Expected intact `skip` and `exact rfl` regions, got: {toString regions}"
  unless spanTexts .warning hl == ["skip overlapping exact rfl"] do
    throwError s!"Expected one warning span reaching the region's end, got: {toString (spanTexts .warning hl)}"
  checkRoundTrip input hl

open Lean Elab Command in
-- A tactic region that reaches its end inside a message stays open until the message closes.
#eval show CommandElabM Unit from do
  let input := String.intercalate "\n" [
    "theorem overlappedRegionTail : 1 + 1 = 2 := by",
    "  overlap_note' exact rfl overlapping skip",
    ""]
  let hl ← highlightModuleStyle input
  let regions := hl.proofStates.toList.map (·.fst)
  unless regions.contains "exact rfl overlapping skip" do
    throwError s!"Expected a region reaching the warning's end, got: {toString regions}"
  unless spanTexts .warning hl == ["rfl overlapping skip"] do
    throwError s!"Expected one warning span covering `rfl overlapping skip`, got: {toString (spanTexts .warning hl)}"
  checkRoundTrip input hl

open Lean Elab Command in
-- A message whose range is exactly a tactic's region wraps that region.
#eval show CommandElabM Unit from do
  let input := String.intercalate "\n" [
    "theorem sameExtent : 1 + 1 = 2 := by",
    "  flag_tac rfl",
    ""]
  let hl ← highlightModuleStyle input
  unless hasSpanWithTactics .warning hl do
    throwError m!"Expected a warning span containing a proof state region:\n{hlStringWithMessages hl}"
  unless spanTexts .warning hl == ["rfl"] do
    throwError s!"Expected the warning to cover `rfl`, got: {toString (spanTexts .warning hl)}"
  checkRoundTrip input hl

open Lean Elab Command in
-- Message ranges that overlap each other and a tactic region close in nesting order.
#eval show CommandElabM Unit from do
  let input := String.intercalate "\n" [
    "theorem crossedMessages : 1 + 1 = 2 := by",
    "  crossed_notes skip with exact rfl",
    ""]
  let hl ← highlightModuleStyle input
  unless hasNestedSpans .warning .info hl do
    throwError m!"Expected a note span nested in a warning span:\n{hlStringWithMessages hl}"
  unless spanTexts .warning hl == ["skip with exact rfl"] do
    throwError s!"Expected one warning span reaching the region's end, got: {toString (spanTexts .warning hl)}"
  unless spanTexts .info hl == ["exact rfl"] do
    throwError s!"Expected one note span covering `exact rfl`, got: {toString (spanTexts .info hl)}"
  checkRoundTrip input hl

end MessageTacticNesting

/-! # Variable Hover Types -/
section VarHoverTypes

open SubVerso.Highlighting

/-- The `(content, hover type)` of each variable token, in source order. -/
partial def SubVerso.Highlighting.Highlighted.varTokens (hl : Highlighted) : Array (String × String) := Id.run do
  let mut out := #[]
  match hl with
  | .seq hls =>
    for x in hls.map varTokens do
      out := out ++ x
  | .span _ hl' => out := out ++ hl'.varTokens
  | .tactics _ _ _ hl' => out := out ++ hl'.varTokens
  | .token ⟨.var _ ty _, s⟩ => out := out.push (s, ty)
  | _ => pure ()
  out

open Lean Elab Command in
/--
Asserts that highlighting `src` module-style gives the variable tokens whose content is `name`
exactly the hover types `expected`, in source order. Does nothing when `skip` is true — used for
tactic syntax that doesn't exist on this toolchain.
-/
def assertVarHoverTypes (src : String) (name : String) (expected : List String)
    (skip : Bool := false) : CommandElabM Unit := do
  if skip then return
  let found := (← highlightModuleStyle src).varTokens.toList.filter (·.1 == name) |>.map (·.2)
  unless found == expected do
    throwError m!"hover types for '{name}':\n{repr found}\nexpected:\n{repr expected}"

-- A binder can be linked across elaboration contexts that give it different types: in
-- `if h : c then _ else _`, `h` is `c` in the then branch and `¬c` in the else branch. Each
-- occurrence hovers with the type from its own context.
#eval assertVarHoverTypes
  (String.intercalate "\n" [
    "example (n k : Nat) : Decidable (n = k) :=",
    "  if h : n = k then Decidable.isTrue h else Decidable.isFalse h"])
  "h" ["n = k", "n = k", "¬n = k"]

-- Same variable, same type, but the printed form depends on the names in scope at each
-- occurrence: renaming another hypothesis changes how this one's type renders.
#eval assertVarHoverTypes
  (String.intercalate "\n" [
    "example (x : Nat) (h : x = x) : True := by",
    "  have _ : x = x := h",
    "  rename Nat => y",
    "  have _ : y = y := h",
    "  trivial"])
  "h" ["x = x", "x = x", "y = y"]

end VarHoverTypes

/-! # Point Diagnostic Extents -/
section PointDiagnosticExtents

open SubVerso.Highlighting

open Lean in
/-- An error at `pos` with no end position, as Lean reports e.g. `unknown tactic`. -/
def pointError (pos : Position) (text : String) : Message :=
  { fileName := "<input>", pos, endPos := none, severity := .error,
    data := toMessageData text }

open Lean Elab Command in
/--
Highlights `input` the way batched code blocks are highlighted (`highlightMany` with unparsed
regions included), passing `messages` directly. `keepCommands` limits how many parsed commands are
given to the highlighter; the text of the rest becomes an unparsed region.
-/
def highlightManyWithMessages (input : String) (messages : Array Message)
    (keepCommands : Option Nat := none) : CommandElabM Highlighting.Highlighted := do
  let inputCtx := Parser.mkInputContext input "<input>"
  let commandState : Command.State := { env := (← getEnv), maxRecDepth := (← get).maxRecDepth }
  let (result, _) ← Compat.Frontend.processCommands mkNullNode
    |>.run { inputCtx } |>.run { commandState, parserState := {}, cmdPos := 0 }
  let items := result.items.filter (·.commandSyntax.getKind != ``Lean.Parser.Command.eoi)
  let items := match keepCommands with
    | some n => items.extract 0 n
    | none => items
  let cmds := items.map (·.commandSyntax)
  let trees := items.map (·.info.toArray[0]?)
  runTermElabM fun _ =>
    withTheReader Core.Context (fun ctx => { ctx with fileMap := inputCtx.fileMap }) do
      let hls ← Highlighting.highlightMany cmds messages trees (includeUnparsed := true)
        (startPos? := cmds[0]!.getPos?) (endPos? := some (Compat.String.endPos input))
      return hls.foldl (init := Highlighting.Highlighted.empty) (· ++ ·)

open Lean Elab Command in
def assertMessageSpans (input : String) (messages : Array Message) (expected : String)
    (keepCommands : Option Nat := none) : CommandElabM Unit := do
  let hl ← highlightManyWithMessages input messages keepCommands
  let found := hlStringWithMessages hl
  unless found == expected do
    throwError m!"Mismatched output\n---Found:---\n{found}\n---Expected:---\n{expected}"

-- A point diagnostic inside a token annotates that token.
#eval assertMessageSpans
  "def one : Nat := 11111\nexample : Nat := one\n"
  #[pointError ⟨1, 19⟩ "subverso_test: point"]
  "def one : Nat := [error: subverso_test: point](11111)\nexample : Nat := one\n"

-- The same when the rest of the input is an unparsed region: the annotation stays on the token
-- rather than covering the region.
#eval assertMessageSpans
  "def one : Nat := 11111\nexample : Nat := one\n"
  #[pointError ⟨1, 19⟩ "subverso_test: point"]
  "def one : Nat := [error: subverso_test: point](11111)\nexample : Nat := one\n"
  (keepCommands := some 1)

-- A point diagnostic inside an unparsed region annotates the whitespace-delimited word at its
-- position.
#eval assertMessageSpans
  "def one : Nat := 11111\nexample : Nat := one\n"
  #[pointError ⟨2, 0⟩ "subverso_test: point"]
  "def one : Nat := 11111\n[error: subverso_test: point](example) : Nat := one\n"
  (keepCommands := some 1)

-- A point diagnostic past its command's last token has no content in that command to annotate, and
-- becomes a point at the command's end rather than annotating a later command.
#eval assertMessageSpans
  "def one : Nat := 11111\nexample : Nat := one\n"
  #[pointError ⟨1, 22⟩ "subverso_test: point"]
  "def one : Nat := 11111\n[point error: subverso_test: point]example : Nat := one\n"

end PointDiagnosticExtents

/-! # Constant Signature Rendering -/
section ConstSignatures

open SubVerso.Highlighting

/-- The `(content, signature)` of each constant token, in source order. -/
partial def SubVerso.Highlighting.Highlighted.constTokens (hl : Highlighted) : Array (String × String) := Id.run do
  let mut out := #[]
  match hl with
  | .seq hls =>
    for x in hls.map constTokens do
      out := out ++ x
  | .span _ hl' => out := out ++ hl'.constTokens
  | .tactics _ _ _ hl' => out := out ++ hl'.constTokens
  | .token ⟨.const _ sig _ _ _, s⟩ => out := out.push (s, sig)
  | _ => pure ()
  out

open Lean Elab Command in
/--
Asserts that batch-highlighting `input` gives the constant tokens whose content is `name` exactly
the signatures `expected`, in source order. Does nothing when `skip` is true.
-/
def assertConstSigs (input : String) (name : String) (expected : List String)
    (skip : Bool := false) : CommandElabM Unit := do
  if skip then return
  let hl ← highlightManyWithMessages input #[]
  let found := hl.constTokens.toList.filter (·.1 == name) |>.map (·.2)
  unless found == expected do
    throwError m!"signatures for '{name}':\n{repr found}\nexpected:\n{repr expected}"

-- On toolchains up to and including 4.5, `PrettyPrinter.ppSignature` renders only a declaration's
-- type, without its name and binders, so the signature strings expected below appear from 4.6 on.
def oldSignatureFormat : Bool :=
  Lean.version.major == 4 && Lean.version.minor <= 5

-- A constant's hover signature renders the names in its type as abbreviated by the namespace and
-- open declarations in force at each occurrence: `N.T` appears as `T` inside `namespace N` and as
-- `N.T` outside it.
#eval assertConstSigs
  (String.intercalate "\n" [
    "namespace N",
    "inductive T where",
    "  | mk",
    "def foo : T := T.mk",
    "end N",
    "def baz : N.T := N.foo",
    ""])
  "foo" ["N.foo : T"]
  (skip := oldSignatureFormat)

#eval assertConstSigs
  (String.intercalate "\n" [
    "namespace N",
    "inductive T where",
    "  | mk",
    "def foo : T := T.mk",
    "end N",
    "def baz : N.T := N.foo",
    ""])
  "N.foo" ["N.foo : N.T"]
  (skip := oldSignatureFormat)

end ConstSignatures

def main : IO Unit := pure ()
