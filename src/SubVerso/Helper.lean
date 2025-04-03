/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json
import SubVerso.Highlighting
import SubVerso.Helper.Netstring

open Lean ToJson FromJson
open SubVerso.Highlighting

namespace SubVerso.Helper

/-
This is a synchronous subset of JSON-RPC (someday this might want to go full async, so this will
provide an easier migration path)
-/
inductive Request where
  | term (code : String) (type? : Option String)
  | exit
deriving Repr

inductive Result where
  | highlighted (code : Highlighted)
deriving Repr

section
local instance : Repr Json := ⟨fun x _ => toString x⟩
inductive Response where
  | result (res : Result)
  | error (code : Nat) (message : String) (data : Option Json)
deriving Repr
end

instance : ToJson Request where
 toJson
    | .term code type? =>
      let params : Json :=
        .mkObj <| [("code", .str code)] ++ (type?.map (fun t => [("type", .str t)])).getD []
      .mkObj [("method", .str "term"), ("params", params)]
    | .exit => .mkObj [("method", .str "exit"), ("params", .mkObj [])]

instance : FromJson Request where
  fromJson? v := do
    let m ← v.getObjValAs? String "method"
    match m with
    | "term" =>
      let params ← v.getObjVal? "params"
      let code ← params.getObjValAs? String "code"
      let type := params.getObjVal? "type" |>.toOption
      let type ← type.mapM (·.getStr?)
      return .term code type
    | "exit" => return .exit
    | _ => throw s!"Didn't understand method '{m}'"

instance : ToJson Result where
  toJson
    | .highlighted hl => .mkObj [("highlighted", toJson hl)]

instance : FromJson Result where
  fromJson? v := do
    let hl := v.getObjValD "highlighted"
    if hl != .null then
      return (← .highlighted <$> fromJson? hl)

    throw "Expected key 'highlighted'"

instance : ToJson Response where
  toJson
    | .result res => .mkObj [("result", toJson res)]
    | .error code msg data =>
      let dataField :=
        match data with
        | none => []
        | some v => [("data", v)]
      .mkObj [("error", .mkObj <| [("code", toJson code), ("message", toJson msg)] ++ dataField)]

instance : FromJson Response where
  fromJson? v := do
    let result := v.getObjValD "result"
    let err := v.getObjValD "error"
    if result != .null && err != .null then
      throw "Got both 'result' and 'error' keys, expected exactly one"
    else if result != .null then
      return (← .result <$> fromJson? result)
    else if err != .null then
      let data := err.getObjVal? "data" |>.toOption
      return (← .error <$> err.getObjValAs? _ "code" <*> err.getObjValAs? _ "message" <*> pure data)
    else throw "Expected 'result' or 'error' key"

def send [ToJson α] (stream : IO.FS.Stream) (message : α) : IO Unit :=
  let json := toJson message |>.compress |>.toUTF8
  writeNetstring stream json

def sendThe (α) [ToJson α] (stream : IO.FS.Stream) (message : α) : IO Unit := send stream message

def receive [FromJson α] (stream : IO.FS.Stream) : IO (Option α) := do
  let some str ← readNetstring stream
    | return none
  let str := String.fromUTF8! str
  let json ← IO.ofExcept (Json.parse str)
  IO.ofExcept (fromJson? json)

def receiveThe (α) [FromJson α] (stream : IO.FS.Stream) : IO (Option α) := receive stream
