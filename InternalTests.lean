
import SubVerso.Examples
import SubVerso.Highlighting.Highlighted
import SubVerso.Highlighting.Anchors

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
      | throwError "Too many messages"
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
      | throwError "Too many messages"
    let ok := ss.getElems.toList.map (·.getString)
    if (← msg.toString) ∉ ok then
      throwErrorAt e "Expected one of {ok.map String.quote}, got {String.quote (← msg.toString)}"
  finally
    modify ({· with messages := msgs})

#evalString "[[\"n * 1 = n\"]]\n"
  (proofEx.highlighted[0].proofStates.toList.filter (·.fst == "by") |>.map (·.snd.toList.map (·.conclusion)))

#evalStrings [ -- NB #5677 changed goal displays, so the second
               -- version here became the expected output after
               -- nightly-2024-10-18.
    "[[some \"zero\"], [some \"succ\"], [none], [some \"succ.succ\"], [none]]\n",
    "[[none], [some \"succ.succ\"], [none]]\n"]
 (proofEx.highlighted[0].proofStates.toList.filter (·.fst == "=>") |>.map (·.snd.toList.map (·.name)))

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
  | .point .. => ""
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
  "[info: subverso_test: 1](deriving )[info: subverso_test: 1](a bunch) of [info: subverso_test: 4]([info: subverso_test: 2](other) [info: subverso_test: 3](filler) [info: subverso_test: 5](text def b)) := true

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
def highlightModuleStyle (input : String) : CommandElabM Highlighting.Highlighted := do
  let inputCtx := Parser.mkInputContext input "<input>"
  let commandState : Command.State := { env := (← getEnv), maxRecDepth := (← get).maxRecDepth }
  let commandState :=
    let sc := commandState.scopes[0]!
    { commandState with scopes := { sc with opts := sc.opts.setBool `pp.tagAppFns true } :: commandState.scopes.tail! }
  let (result, _) ← Compat.Frontend.processCommands mkNullNode
    |>.run { inputCtx } |>.run { commandState, parserState := {}, cmdPos := 0 }
  let result := result.updateLeading input
  runTermElabM fun _ =>
    withTheReader Core.Context (fun ctx => { ctx with fileMap := inputCtx.fileMap }) do
      let hls ← Highlighting.highlightFrontendResult result
      return hls.foldl (· ++ ·) .empty

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
`#assertTacticKind inp kind` parses `inp` as a tactic and checks its syntax kind is `kind`.

The highlighter special-cases certain tactics (`have`, `obtain`, …) by their syntax kind. The kinds
themselves are referenced with ``…`` in `findTactics`, so a *missing* name is caught at compile time;
these assertions cover the other half — that the (sometimes auto-generated) name still denotes the
tactic of interest. If a toolchain makes `have`/`obtain` parse to a different kind, this fails in CI
for that toolchain, pointing at the kind in `findTactics` that needs updating.
-/
elab "#assertTacticKind" inp:str kind:str : command => do
  match Parser.runParserCategory (← getEnv) `tactic inp.getString with
  | .error e => throwError m!"failed to parse tactic {repr inp.getString}: {e}"
  | .ok stx =>
    unless stx.getKind == kind.getString.toName do
      throwError m!"tactic {repr inp.getString} parses to kind {stx.getKind}, expected \
        {kind.getString}; update the highlighter's special-cased kind for this Lean toolchain"

-- The highlighter attaches whole-tactic proof-state regions to these tactics by keying on these
-- exact syntax kinds (see `findTactics`). These guard that the names still denote those tactics
-- (and the `assertStateTree` tests below guard the resulting behavior).
#assertTacticKind "have h : Nat := by exact 0" "Lean.Parser.Tactic.tacticHave__"
#assertTacticKind "obtain ⟨a, b⟩ := h" "Lean.Parser.Tactic.obtain"
#assertTacticKind "let x : Nat := by exact 0" "Lean.Parser.Tactic.tacticLet__"
#assertTacticKind "suffices h : Nat by trivial" "Lean.Parser.Tactic.tacticSuffices_"
#assertTacticKind "replace h : Nat := by exact 0" "Lean.Parser.Tactic.replace"

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

open Lean Elab Command in
/-- Asserts the nested proof-state tree of `src` (highlighted module-style) equals `expected`. -/
def assertStateTree (src : String) (expected : List (Nat × String × List String)) : CommandElabM Unit := do
  let tree := (← highlightModuleStyle src).stateTree.toList
  unless tree == expected do
    throwError m!"proof-state tree =\n{repr tree}\nexpected\n{repr expected}"

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
-- `replace` shows the state after it and the macro-mangled nested `by` state is dropped, leaving the
-- subproof's real steps.
open Lean Elab Command in
#eval assertStateTree
  "example (h : Nat) : True := by\n  replace h : Int := by exact 0\n  trivial"
  [(0, "by", ["True"]),
   (0, "replace h : Int := by exact 0", ["True"]),
     (1, "exact 0", []),
   (0, "trivial", [])]

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
-- it (the goal with `h` added), with the subproof's steps nested inside at depth 1. The subproof's
-- own `by` token shows *no* state: `have` is a macro, and its embedded `by` is recorded with the
-- enclosing goal rather than the subproof's, so that initial state would just repeat the enclosing
-- conclusion — it is dropped by `conclusionsDuplicateOpen`, while the real steps survive.
open Lean Elab Command in
#eval assertStateTree
  "example : True := by\n  have h : 2 = 2 := by rfl\n  trivial"
  [(0, "by", ["True"]),
   (0, "have h : 2 = 2 := by rfl", ["True"]),
     (1, "rfl", []),
   (0, "trivial", [])]
-- A multi-step subproof keeps every nested step (and still drops the spurious nested-`by` state).
open Lean Elab Command in
#eval assertStateTree
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
open Lean Elab Command in
#eval assertStateTree
  "example : True := by\n  obtain ⟨k, hk⟩ := id (α := ∃ k : Nat, k = 0) (by exact ⟨0, rfl⟩)\n  trivial"
  [(0, "by", ["True"]),
   (0, "obtain ⟨k, hk⟩ := id (α := ∃ k : Nat, k = 0) (by exact ⟨0, rfl⟩)", ["True"]),
     (1, "by", ["∃ k, k = 0"]),
     (1, "exact ⟨0, rfl⟩", []),
   (0, "trivial", [])]

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

-- `:=` stays a `.delim` across contexts even on the info-recording path, where `identKind` could
-- otherwise match its span: a structure-instance field, an `instance … where` field, and a tactic
-- `have` all keep it a delim (it is peeled off before `identKind` is consulted).
#assertKindRich "structure S where\n  x : Nat\n#check ({ x := 1 } : S)" ":=" "delim"
#assertKindRich "class C (a : Type) where\n  f : a → a\ninstance : C Nat where\n  f x := x" ":=" "delim"
#assertKindRich "theorem t : True := by\n  have h : True := trivial\n  exact h" ":=" "delim"

end TokenKinds

def main : IO Unit := pure ()
