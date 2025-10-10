/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import SubVerso.Compat
public section

namespace SubVerso.Examples.Messages

private inductive NormMetavarState where
  /-- Not looking at a metavar -/
  | none
  /-- Saw the leading '?' -/
  | «?» (iter : String.Iterator)
  /-- Saw the '?m' or '?u' -/
  | «?m/u» (ch : Char) (iter : String.Iterator)
  /-- Saw the '?[mu].' -/
  | «?m/u.» (ch : Char) (iter : String.Iterator)
  /-- Saw one or more digits - '?m.[0-9]+' -/
  | «?m/u.[0-9]+» (ch : Char) (iter : String.Iterator)

/--
Consistently rewrite all substrings that look like automatic metavariables (e.g "?m.123") so
that they're ?m.1, ?m.2, etc.
-/
def normalizeMetavars (str : String) : String := Id.run do
  let mut out := ""
  let mut iter := str.iter
  let mut gensymCounter := 1
  let mut nums : Compat.HashMap String Nat := {}
  let mut state : NormMetavarState := .none
  while h : iter.hasNext do
    let c := iter.curr' h

    match state with
    | .none =>
      if c == '?' then
        state := .«?» iter
      else
        out := out.push c
    | .«?» i =>
      if c == 'm' || c == 'u' then
        state := .«?m/u» c i
      else
        state := .none
        out := out.push '?'
        out := out.push c
    | .«?m/u» c' i =>
      state := if c == '.' then .«?m/u.» c' i else .none
    | .«?m/u.» c' i =>
      state := if c.isDigit then .«?m/u.[0-9]+» c' i else .none
    | .«?m/u.[0-9]+» c' i =>
      unless c.isDigit do
        state := .none
        let mvarStr := i.extract iter
        match nums[mvarStr]? with
        | none =>
          nums := nums.insert mvarStr gensymCounter
          out := out ++ s!"?{c'}.{gensymCounter}"
          gensymCounter := gensymCounter + 1
        | some s => out := out ++ s!"?{c'}.{s}"
        out := out.push c

    iter := iter.next

  match state with
  | .«?m/u.[0-9]+» c' i =>
    let mvarStr := i.extract iter
    match nums[mvarStr]? with
    | none =>
      nums := nums.insert mvarStr gensymCounter
      out := out ++ s!"?{c'}.{gensymCounter}"
      gensymCounter := gensymCounter + 1
    | some s => out := out ++ s!"?{c'}.{s}"
  | .«?» i  | .«?m/u» _c' i | .«?m/u.» _c' i =>
    out := out ++ i.extract iter
  | .none => pure ()

  out
