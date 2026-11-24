/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Compat
import SubVerso.Module

open Lean

namespace SubVerso.Module

private structure Renaming where
  names : Compat.HashMap String String := {}
  next : Nat := 1

private abbrev RenameM := StateM Renaming

private def rename (name : String) : RenameM String := do
  if let some n := (← get).names.get? name then
    return n
  modifyGet fun s =>
    let n := s!"v{s.next}"
    (n, { s with names := s.names.insert name n, next := s.next + 1 })

private inductive JsonPosition where
  | plain
  | varFields
  | varName

private def childPosition (pos : JsonPosition) (key : String) : JsonPosition :=
  match pos, key with
  | _, "var" => .varFields
  | .varFields, "name" => .varName
  | _, _ => .plain

private partial def renameVars (pos : JsonPosition) (json : Json) : RenameM Json := do
  match json with
  | .arr xs => .arr <$> xs.mapM (renameVars .plain)
  | .str s =>
    match pos with
    | .varName => .str <$> rename s
    | _ => pure json
  | _ =>
    match Compat.Json.objectFields? json with
    | some fields =>
      let fields ← fields.mapM fun (k, v) => do return (k, ← renameVars (childPosition pos k) v)
      return Json.mkObj fields.toList
    | none => pure json

private def normalizeItem (item : ModuleItem) : Json :=
  Id.run ((renameVars .plain (toJson item)).run' {})

def normalize (mod : Module) : Json :=
  .arr (mod.items.map normalizeItem)
