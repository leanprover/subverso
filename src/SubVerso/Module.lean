/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Position
import Lean.Data.Json
public import SubVerso.Highlighting

public section

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
A single textual replacement performed by a code action. Both ranges denote the same absolute
region of the document: `range` as line/column positions and `utf8Range` as byte offsets into the
UTF-8 encoding of the source. The region may lie anywhere in the document, including outside the
command where the action is offered.
-/
structure SuggestedEdit where
  range : Lean.Position × Lean.Position
  utf8Range : Nat × Nat
  newText : String
deriving Inhabited, Repr, BEq

/--
A code action offered somewhere in a module, with its edits fully computed. `range` and
`utf8Range` both denote the source range of the command at which the action is offered.
-/
structure CodeAction where
  range : Lean.Position × Lean.Position
  utf8Range : Nat × Nat
  title : String
  kind? : Option String := none
  isPreferred : Bool := false
  edits : Array SuggestedEdit
deriving Inhabited, Repr, BEq

def utf8RangeToJson : Nat × Nat → Json
  | (s, e) => Json.mkObj [("start", s), ("end", e)]

def utf8RangeFromJson (json : Json) : Except String (Nat × Nat) := do
  let s ← json.getObjValAs? Nat "start"
  let e ← json.getObjValAs? Nat "end"
  pure (s, e)

def requiredRangeFromJson (json : Json) : Except String (Lean.Position × Lean.Position) := do
  let some range ← rangeFromJson json
    | throw "Expected a range, got null"
  pure range

def SuggestedEdit.toJson : SuggestedEdit → Json
  | {range, utf8Range, newText} =>
    Json.mkObj [
      ("range", rangeToJson range),
      ("utf8Range", utf8RangeToJson utf8Range),
      ("newText", ToJson.toJson newText)
    ]

def SuggestedEdit.fromJson? (json : Json) : Except String SuggestedEdit := do
  let range ← json.getObjVal? "range" >>= requiredRangeFromJson
  let utf8Range ← json.getObjVal? "utf8Range" >>= utf8RangeFromJson
  let newText ← json.getObjValAs? String "newText"
  return {range, utf8Range, newText}

instance : ToJson SuggestedEdit := ⟨SuggestedEdit.toJson⟩
instance : FromJson SuggestedEdit := ⟨SuggestedEdit.fromJson?⟩

def CodeAction.toJson : CodeAction → Json
  | {range, utf8Range, title, kind?, isPreferred, edits} =>
    Json.mkObj [
      ("range", rangeToJson range),
      ("utf8Range", utf8RangeToJson utf8Range),
      ("title", ToJson.toJson title),
      ("kind", kind?.map ToJson.toJson |>.getD .null),
      ("isPreferred", ToJson.toJson isPreferred),
      ("edits", ToJson.toJson edits)
    ]

def CodeAction.fromJson? (json : Json) : Except String CodeAction := do
  let range ← json.getObjVal? "range" >>= requiredRangeFromJson
  let utf8Range ← json.getObjVal? "utf8Range" >>= utf8RangeFromJson
  let title ← json.getObjValAs? String "title"
  let kind? ← match json.getObjVal? "kind" with
    | .ok .null | .error _ => pure none
    | .ok v => some <$> FromJson.fromJson? (α := String) v
  let isPreferred := json.getObjValAs? Bool "isPreferred" |>.toOption |>.getD false
  let edits ← json.getObjValAs? (Array SuggestedEdit) "edits"
  return {range, utf8Range, title, kind?, isPreferred, edits}

instance : ToJson CodeAction := ⟨CodeAction.toJson⟩
instance : FromJson CodeAction := ⟨CodeAction.fromJson?⟩

/--
A sequence of module items, together with the code actions offered in the module. The JSON
instances for this type produce output that is much more compact than the underlying array.
-/
structure Module where
  items : Array ModuleItem
  codeActions : Array CodeAction := #[]
deriving Inhabited

def Module.toJson (mod : Module) : Json :=
  let (items, state) := mod.items.mapM itemJson |>.run {}
  Json.mkObj [
    ("data", state.toExport.toJson),
    ("items", .arr items),
    ("codeActions", ToJson.toJson mod.codeActions)
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
  let codeActions : Array CodeAction ←
    (json.getObjVal? "codeActions").toOption.map Lean.FromJson.fromJson? |>.getD (pure #[])
  let items ← items.mapM (getItem data)
  return { items, codeActions }
where
  getItem (data : Export) (v : Json) : Except String ModuleItem := do
    let range ← v.getObjVal? "range" >>= rangeFromJson
    let kind ← v.getObjValAs? String "kind" <&> (·.toName)
    let defines ← v.getObjValAs? (Array String) "defines" <&> (·.map (·.toName))
    let code ← v.getObjValAs? Export.Key "code"
    let code ← data.toHighlighted code
    return {range, kind, defines, code}

instance : FromJson Module := ⟨Module.fromJson?⟩
