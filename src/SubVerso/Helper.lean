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

set_option linter.missingDocs true

namespace SubVerso.Helper

/-!
This is a synchronous subset of JSON-RPC (someday this might want to go full async, so this will
provide an easier migration path)
-/

/--
Requests that clients can make to the helper
-/
inductive Request where
  /-- A request to elaborate a term in the present environment. -/
  | term (code : String) (type? : Option String)
  /-- A request to look up a name in the present environment. -/
  | name (code : String)
  /-- A request to run a command in the present environment. -/
  | command (code : String)
  /-- A request to check and highlight a signature -/
  | signature (code : String)
  /-- A request that the process terminate -/
  | exit
deriving Repr


/--
Replies that the helper may return.
-/
inductive Result where
  /-- Highlighted Lean code -/
  | highlighted (code : Highlighted)
deriving Repr

section
local instance : Repr Json := ⟨fun x _ => toString x⟩
/-- Responses to requests may be either valid results or errors. -/
inductive Response where
  /-- The requested task was completed, and a result was returned. -/
  | result (res : Result)
  /-- The requested task was not completed. -/
  | error (code : Nat) (message : String) (data : Option Json)
deriving Repr
end

instance : ToJson Request where
 toJson
    | .term code type? =>
      let params : Json :=
        .mkObj <| [("code", .str code)] ++ (type?.map (fun t => [("type", .str t)])).getD []
      .mkObj [("method", .str "term"), ("params", params)]
    | .name code =>
      let params : Json := .mkObj [("code", .str code)]
      .mkObj [("method", .str "name"), ("params", params)]
    | .command code =>
      let params : Json := .mkObj [("code", .str code)]
      .mkObj [("method", .str "command"), ("params", params)]
    | .signature code =>
      let params : Json := .mkObj [("code", .str code)]
      .mkObj [("method", .str "signature"), ("params", params)]
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
    | "name" =>
      let params ← v.getObjVal? "params"
      let code ← params.getObjValAs? String "code"
      return .name code
    | "command" =>
      let params ← v.getObjVal? "params"
      let code ← params.getObjValAs? String "code"
      return .command code
    | "signature" =>
      let params ← v.getObjVal? "params"
      let code ← params.getObjValAs? String "code"
      return .signature code
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

/-- Sends a message on a stream, encoded in JSON and transported via netstrings. -/
def send [ToJson α] (stream : IO.FS.Stream) (message : α) : IO Unit :=
  let json := toJson message |>.compress |>.toUTF8
  writeNetstring stream json

/-- Sends a message of the indicated type on a stream, encoded in JSON and transported via netstrings. -/
def sendThe (α) [ToJson α] (stream : IO.FS.Stream) (message : α) : IO Unit := send stream message

/-- Reads a JSON-encoded message from a stream of netstrings. -/
def receive [FromJson α] (stream : IO.FS.Stream) : IO (Option α) := do
  let some str ← readNetstring stream
    | return none
  let str := Compat.decodeUTF8 str
  let json ← IO.ofExcept (Json.parse str)
  IO.ofExcept (fromJson? json)

/-- Reads a JSON-encoded message of the given type from a stream of netstrings. -/
def receiveThe (α) [FromJson α] (stream : IO.FS.Stream) : IO (Option α) := receive stream
