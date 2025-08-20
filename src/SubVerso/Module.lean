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
deriving Inhabited

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

/--
A sequence of module items. The JSON instances for this type produce output that is much more
compact than the underlying array.
-/
structure Module where
  items : Array ModuleItem
deriving Inhabited

def Module.toJson (mod : Module) : Json :=
  let (items, state) := mod.items.mapM itemJson |>.run {}
  Json.mkObj [
    ("data", state.toExport.toJson),
    ("items", .arr items)
  ]
where
  itemJson : ModuleItem → ExportM Json
    | {range, kind, defines, code} => do
      return Json.mkObj [
        ("range", range.map rangeToJson |>.getD .null),
        ("kind", ToJson.toJson <| toString kind),
        ("defines", ToJson.toJson <| defines.map toString),
        ("code", ToJson.toJson (← code.export))
      ]

instance : ToJson Module := ⟨Module.toJson⟩

def Module.fromJson? (json : Json) : Except String Module := do
  let data ← json.getObjVal? "data"
  let data ← Export.fromJson? data
  let .arr items ← json.getObjVal? "items"
    | throw "Expected array for key 'items'"
  return ⟨← items.mapM (getItem data)⟩
where
  getItem (data : Export) (v : Json) : Except String ModuleItem := do
    let range ← v.getObjVal? "range" >>= rangeFromJson
    let kind ← v.getObjValAs? String "kind" <&> (·.toName)
    let defines ← v.getObjValAs? (Array String) "defines" <&> (·.map (·.toName))
    let code ← v.getObjValAs? Export.Key "code"
    let code ← data.toHighlighted code
    return {range, kind, defines, code}

instance : FromJson Module := ⟨Module.fromJson?⟩
