
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
  | .const .. => "const"
  | .anonCtor .. => "anonCtor"
  | .var .. => "var"
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

/-- Whether the highlighted tree contains a `.tactics` (proof-state) wrapper. -/
partial def Highlighted.hasTactics : Highlighted → Bool
  | .tactics .. => true
  | .seq hls => hls.any Highlighted.hasTactics
  | .span _ hl => hl.hasTactics
  | _ => false

/-- The occurrence tag of a production-bearing token kind, if any. -/
def Token.Kind.occurrence? : Token.Kind → Option String
  | .keyword _ occ _ | .operator _ occ _ | .bracket _ occ _ | .separator _ occ _ => occ
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

-- Core symbolic keywords/delimiters stay `.keyword`, not `.operator`
#assertKind "def x := 1" ":=" "keyword"
#assertKind "def f := fun (x : Nat) => x" "=>" "keyword"

-- Module docs are tagged like doc comments
#assertHasKind "/-! module doc -/" "docComment"

-- The derived `ToJson`/`FromJson` instances round-trip every new token kind
#evalString "true\n"
  (([Token.Kind.num (some "Nat") none, .num none none, .char 'a', .lineComment, .blockComment,
     .commentDelim, .operator (some `foo) (some "foo-1") (some "d"), .bracket none none none,
     .separator none none none] : List Token.Kind).all (fun k => Token.jsonRoundtrips ⟨k, "x"⟩))

-- The new `identKind`-first atom step: a nullary notation atom (`ℕ`) resolves span-exact to its
-- constant (`.const`), while a genuine infix operator (`+`) has no span-exact info and stays
-- `.operator`. Both require the info-recording highlight path (`#assertKindRich`), as in real
-- extraction; this needs no Mathlib — a local `notation` suffices.
#assertKindRich "notation \"ℕ\" => Nat\ndef m : ℕ := 0" "ℕ" "const"
#assertKindRich "def f (a b : Nat) := a + b" "+" "operator"
#assertKind "def x := 1" ":=" "keyword"

end TokenKinds

def main : IO Unit := pure ()
