
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
    "[[some `zero], [some `succ], [none], [some `succ.succ], [none]]\n",
    "[[none], [some `succ.succ], [none]]\n"]
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

def main : IO Unit := pure ()
