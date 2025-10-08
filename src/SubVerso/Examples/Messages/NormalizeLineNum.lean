/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import SubVerso.Compat
public section

open SubVerso Compat

namespace SubVerso.Examples.Messages

private inductive State where
  /-- Just saw a newline -/
  | nl
  /-- Just saw a newline then one or more digits -/
  | «nl[0-9]+»
  /-- Just saw a newline then one or more digits then a right-paren -/
  | «nl[0-9]+)»
  /-- Just saw a newline then one or more digits then right-paren then a space -/
  | «nl[0-9]+) »
  /-- Just saw a newline then one or more digits then right-paren then a space then one or more digits -/
  | «nl[0-9]+) [0-9]+» (line : Nat)
  /-- None of the above -/
  | none

/--
Normalizes the line numbers that occur in recursion issues for less-fragile comparisons.
-/
def normalizeLineNums (str : String) : String := Id.run do
  let mut assignments : HashMap Nat Nat := {}
  let mut next := 0
  let mut iter := str.iter
  let mut state : State := .nl
  let mut out : String := ""
  while h : iter.hasNext do
    let c := iter.curr' h
    iter := iter.next' h
    match state with
    | .nl =>
      out := out.push c
      if c.isDigit then
        state := .«nl[0-9]+»
      else
        state := .none
    | .«nl[0-9]+» =>
      out := out.push c
      if c == ')' then
        state := .«nl[0-9]+)»
      else if !c.isDigit then
        state := .none
    | .«nl[0-9]+)» =>
      out := out.push c
      if c == ' ' then
        state := .«nl[0-9]+) »
      else
        state := .none
    | .«nl[0-9]+) » =>
      if c.isDigit then
        state := .«nl[0-9]+) [0-9]+» (String.toNat! s!"{c}")
      else
        out := out.push c
        state := .none

    | .«nl[0-9]+) [0-9]+» l =>
      if c.isDigit then
        state := .«nl[0-9]+) [0-9]+» ((l * 10) + (String.toNat! s!"{c}"))
      else
        if let some l' := assignments[l]? then
          out := out ++ s!"L{l'}"
        else
          next := next + 1
          assignments := assignments.insert l next
          out := out ++ s!"L{next}"
        out := out.push c
        state := .none
    | .none =>
      out := out.push c
      if c == '\n' then state := .nl
  if let .«nl[0-9]+) [0-9]+» l := state then
    out := out ++ s!"{l}"
  return out
