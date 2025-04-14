/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Position
import Lean.Data.Json
import SubVerso.Highlighting

open Lean ToJson FromJson
open SubVerso.Highlighting

namespace SubVerso.Module

structure ModuleItem where
  range : Option (Lean.Position × Lean.Position)
  kind : SyntaxNodeKind
  defines : Array Name
  code : Highlighted

def ModuleItem.start (item : ModuleItem) : Option Lean.Position := item.range.map (·.1)
def ModuleItem.stop (item : ModuleItem) : Option Lean.Position := item.range.map (·.2)

def positionToJson : Lean.Position → Json
  | {line, column} => Json.mkObj [("line", line), ("column", (column + 1 : Nat))]

def positionFromJson (json : Json) : Except String Lean.Position := do
  let line ← json.getObjValAs? Nat "line"
  let col ← json.getObjValAs? Nat "column"
  pure {line, column := col - 1}

def rangeToJson : Lean.Position × Lean.Position → Json
  | (s, e) => Json.mkObj [("start", positionToJson s), ("end", positionToJson e)]

def rangeFromJson (json : Json) : Except String (Option (Lean.Position × Lean.Position)) := do
  if json.isNull then pure none
  else
    let s ← json.getObjVal? "start"
    let e ← json.getObjVal? "end"
    pure (some ⟨← positionFromJson s, ← positionFromJson e⟩)

def ModuleItem.toJson : ModuleItem → Json
  | {range, kind, defines, code} =>
    Json.mkObj [
      ("range", range.map rangeToJson |>.getD .null),
      ("kind", ToJson.toJson <| toString kind),
      ("defines", ToJson.toJson <| defines.map toString),
      ("code", ToJson.toJson code)
    ]

def ModuleItem.fromJson? (json : Json) : Except String ModuleItem := do
  let range ← json.getObjVal? "range" >>= rangeFromJson
  let kind ← json.getObjValAs? String "kind" <&> (·.toName)
  let defines ← json.getObjValAs? (Array String) "defines" <&> (·.map (·.toName))
  let code ← json.getObjValAs? _ "code"
  return {range, kind, defines, code}

instance : ToJson ModuleItem := ⟨ModuleItem.toJson⟩
instance : FromJson ModuleItem := ⟨ModuleItem.fromJson?⟩
