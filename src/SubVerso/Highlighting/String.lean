/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Highlighting.Highlighted
import SubVerso.Compat

namespace SubVerso.Highlighting.Highlighted

/--
Finds the first name `Token` whose string representation matches the given name exactly.

Name tokens are those with kind `const` or `var`.
-/
partial def matchingName? (hl : Highlighted) (name : String) : Option Token := do
  match hl with
  | .seq xs => xs.findSome? (matchingName? · name)
  | .point .. | .text .. | .unparsed .. => none
  | .tactics _ _ _ x | .span _ x => matchingName? x name
  | .token t@⟨k, s⟩ =>
    match k with
    | .const .. | .var .. => if s == name then return t else none
    | _ => none

/--
Splits highlighted code into its first token followed by the rest of the code. If the code doesn't
begin with a `.token`, `none` is returned.
-/
partial def firstToken (hl : Highlighted) : Option (Highlighted × Highlighted) :=
  match hl with
  | .seq xs => do
    let mut xs := xs
    repeat
      if let some x := xs[0]? then
        xs := xs.extract 1 xs.size
        if let some (t, xs') := firstToken x then
          return (t, xs' ++ .seq xs)
        else continue
      else failure
    failure
  | .point .. | .text .. | .unparsed .. => none
  | .tactics _ _ _ x | .span _ x => firstToken x
  | .token .. => pure (hl, .empty)

/--
Returns the prefix of `hl` that matches the string `term`. The returned code has whitespace from
`term`.
-/
def matchingExprPrefix? (hl : Highlighted) (term : String) : Option Highlighted := do
  let mut out : Highlighted := .empty
  let mut term : String := term
  let mut hl := hl

  while !term.isEmpty do
    let ws := Compat.String.takeWhile term (·.isWhitespace)
    out := out ++ .text ws
    term := Compat.String.trimLeft term
    let (first, rest) ← firstToken hl
    hl := rest
    let firstStr := first.toString
    let term' ← term.dropPrefix? firstStr
    term := term'.toString
    out := out ++ first
  return out

/--
Returns the first subsequence of `hl` that matches the string `term`. The returned code has
whitespace from `term`.
-/
def matchingExpr? (hl : Highlighted) (term : String) : Option Highlighted := do
  let mut hl := hl
  repeat
    let (first, rest) ← firstToken hl
    hl := rest
    if let some out := matchingExprPrefix? (first ++ rest) term then
      return out

  failure
