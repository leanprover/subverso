
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

def main : IO Unit := pure ()
