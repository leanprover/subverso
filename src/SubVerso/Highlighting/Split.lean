/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Highlighting.Highlighted

namespace SubVerso.Highlighting

open Highlighted in
private inductive SplitCtxF where
  | tactics : Array (Goal Highlighted) → Nat → Nat → SplitCtxF
  | span : Array (Span.Kind × Message Highlighted) → SplitCtxF
deriving Repr

private def SplitCtxF.wrap (hl : Highlighted) : SplitCtxF → Highlighted
  | .tactics g s e => .tactics g s e hl
  | .span xs => .span xs hl

private structure SplitCtx where
  contents : Array (Highlighted × SplitCtxF) := #[]
deriving Inhabited, Repr

private def SplitCtx.push (ctx : SplitCtx) (current : Highlighted) (info : SplitCtxF) : SplitCtx where
  contents := ctx.contents.push (current, info)

private def SplitCtx.pop (ctx : SplitCtx) : SplitCtx where
  contents := ctx.contents.pop

private def SplitCtx.close (ctx : SplitCtx) (current : Highlighted) : Highlighted × SplitCtx :=
  match ctx.contents.back? with
  | none => panic! s!"Popping empty context around '{current.toString}'"
  | some (left, f) => (left ++ f.wrap current, ctx.pop)

private def SplitCtx.split (ctx : SplitCtx) (current : Highlighted) : Highlighted × SplitCtx where
  fst := ctx.contents.foldr (init := current) fun (left, f) curr => left ++ f.wrap curr
  snd := { contents := ctx.contents.map (.empty, ·.2) }

def Highlighted.split (p : String → Bool) (hl : Highlighted) : Array Highlighted := Id.run do
  let mut todo := [some hl]
  let mut out := #[]
  let mut ctx : SplitCtx := {}
  let mut current : Highlighted := .empty
  repeat
    match todo with
    | [] =>
      out := out.push current
      break
    | none :: hs =>
      todo := hs
      let (c, ctx') := ctx.split current
      current := c
      ctx := ctx'.pop
    | some (.seq xs) :: hs =>
      todo := xs.toList.map some ++ hs
    | some this@(.token ⟨_, t⟩) :: hs =>
      todo := hs
      if p t then
        out := out.push current
        current := .empty
      else
        current := current ++ this
    | some this@(.text ..) :: hs | some this@(.point ..) :: hs | some this@(.unparsed ..) :: hs =>
      todo := hs
      current := current ++ this
    | some (.span msgs x) :: hs =>
      todo := some x :: none :: hs
      ctx := ctx.push current (.span msgs)
      current := .empty
    | some (.tactics gs b e x) :: hs =>
      todo := some x :: none :: hs
      ctx := ctx.push current (.tactics gs b e)
      current := .empty

  return out

def Highlighted.lines (hl : Highlighted) : Array Highlighted := Id.run do
  let mut todo := [some hl]
  let mut out := #[]
  let mut ctx : SplitCtx := {}
  let mut current : Highlighted := .empty
  repeat
    match todo with
    | [] =>
      out := out.push current
      break
    | none :: hs =>
      todo := hs
      let (c, ctx') := ctx.close current
      current := c
      ctx := ctx'
    | some (.seq xs) :: hs =>
      todo := xs.toList.map some ++ hs
    | some this@(.token ..) :: hs =>
      todo := hs
      current := current ++ this
    | some this@(.text str) :: hs | some this@(.unparsed str) :: hs =>
      if str.contains '\n' then
        let pre := str.takeWhile (· ≠ '\n') ++ "\n"
        let post := str.drop pre.length
        todo := some (.text post) :: hs
        current := current ++ .text pre
        let (c, ctx') := ctx.split current
        out := out.push c
        current := .empty
        ctx := ctx'
      else
        todo := hs
        current := current ++ this
    | some this@(.point ..) :: hs =>
      todo := hs
      current := current ++ this
    | some (.span msgs x) :: hs =>
      todo := some x :: none :: hs
      ctx := ctx.push current (.span msgs)
      current := .empty
    | some (.tactics gs b e x) :: hs =>
      todo := some x :: none :: hs
      ctx := ctx.push current (.tactics gs b e)
      current := .empty

  return out
