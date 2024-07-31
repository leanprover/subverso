
import SubVerso.Examples
import SubVerso.Highlighting.Highlighted

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

#evalString "[[\"n * 1 = n\"]]\n"
  (proofEx.highlighted[0].proofStates.data.filter (·.fst == "by") |>.map (·.snd.data.map (·.conclusion)))

#evalString "[[some `zero], [some `succ], [none], [some `succ.succ], [none]]\n"
  (proofEx.highlighted[0].proofStates.data.filter (·.fst == "=>") |>.map (·.snd.data.map (·.name)))



def main : IO Unit := pure ()
