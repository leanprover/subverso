/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Data.Json
import SubVerso.Highlighting.Highlighted
import SubVerso.Compat

/-!
This module contains tools for reducing the size of JSON exported from SubVerso.
-/

open SubVerso Highlighting
open Lean

namespace SubVerso.Highlighting.Export

/-- How do we look up values? -/
abbrev Key := Nat

structure Hypothesis where
  names : Array Key
  typeAndVal : Key
deriving Repr, BEq, Hashable, ToJson, FromJson, Inhabited

structure Goal where
  name : Option String
  goalPrefix : String
  hypotheses : Array Hypothesis
  conclusion : Key
deriving Repr, BEq, Hashable, ToJson, FromJson, Inhabited

inductive MessageContents where
  | text : String → MessageContents
  | goal : Key → MessageContents
  | term : Key → MessageContents
  | trace (cls : Name) (msg : Key) (children : Array Key) (collapsed : Bool) : MessageContents
  | append : Array Key → MessageContents
deriving Repr, Inhabited, BEq, Hashable, ToJson, FromJson, Inhabited

inductive Highlighted where
  | token (tok : Key)
  | text (str : String)
  | seq (highlights : Array Key)
  | span (info : Array (Highlighted.Span.Kind × Key)) (content : Key)
  | tactics (info : Array Key) (startPos : Nat) (endPos : Nat) (content : Key)
  | point (kind : Highlighted.Span.Kind) (info : Key)
  | unparsed (str : String)
deriving Repr, Inhabited, BEq, Hashable, ToJson, FromJson, Inhabited

end Export

/--
SubVerso data, split up and de-duplicated.
-/
structure Export where
  nextKey : Export.Key := 0
  tokens : Compat.HashMap Export.Key Token := {}
  messageContents : Compat.HashMap Export.Key Export.MessageContents := {}
  goals : Compat.HashMap Export.Key Export.Goal := {}
  code : Compat.HashMap Export.Key Export.Highlighted := {}

def Export.toJson (data : Export) : Json :=
  Json.mkObj [
    ("nextKey", ToJson.toJson data.nextKey),
    ("tokens", tableJson data.tokens),
    ("messageContents", tableJson data.messageContents),
    ("goals", tableJson data.goals),
    ("code", tableJson data.code)
  ]
where
  tableJson {α} [ToJson α] (info : Compat.HashMap Export.Key α) : Json :=
    info.toArray.foldl (init := Json.mkObj []) fun json ⟨k, v⟩ =>
      json.setObjVal! (toString k) (ToJson.toJson v)

instance : ToJson Export := ⟨Export.toJson⟩

def Export.fromJson? (json : Json) : Except String Export := do
  let nextKey ← json.getObjValAs? Export.Key "nextKey"
  let tokens ← tableOf (← json.getObjVal? "tokens")
  let messageContents ← tableOf (← json.getObjVal? "messageContents")
  let goals ← tableOf (← json.getObjVal? "goals")
  let code ← tableOf (← json.getObjVal? "code")
  return {nextKey, tokens, messageContents, goals, code}
where
  tableOf {α} [FromJson α] (table : Json) : Except String (Compat.HashMap Export.Key α) := do
    let obj := (← table.getObj?).toArray
    obj.foldlM (init := {}) fun tbl ⟨k, v⟩ => do
      return tbl.insert k.toNat! (← FromJson.fromJson? v)

instance : FromJson Export := ⟨Export.fromJson?⟩

structure ExportCode extends Export where
  top : Export.Key

def ExportCode.toJson (data : ExportCode) : Json :=
  data.toExport.toJson |>.setObjVal! "top" data.top

instance : ToJson ExportCode := ⟨ExportCode.toJson⟩

def ExportCode.fromJson? (json : Json) : Except String ExportCode := do
  let e ← Export.fromJson? json
  let top ← json.getObjValAs? Export.Key "top"
  return {e with top}

instance : FromJson ExportCode := ⟨ExportCode.fromJson?⟩

structure Exporting extends Export where
  tokenKeys : Compat.HashMap Token Export.Key := {}
  messageContentsKeys : Compat.HashMap Export.MessageContents Export.Key := {}
  codeKeys : Compat.HashMap Export.Highlighted Export.Key := {}
  goalKeys : Compat.HashMap Export.Goal Export.Key := {}

abbrev ExportM := StateM Exporting

def Token.export (tok : Token) : ExportM Export.Key := do
  if let some k := (← get).tokenKeys.get? tok then
    return k
  else
    modifyGet fun e =>
      let k := e.nextKey
      (k, { e with nextKey := k + 1, tokens := e.tokens.insert k tok, tokenKeys := e.tokenKeys.insert tok k })

mutual
  partial def Highlighted.MessageContents.export (txt : Highlighted.MessageContents Highlighted) : ExportM Export.Key := do
    let txt : Export.MessageContents ←
      match txt with
      | .text s => pure (Export.MessageContents.text s)
      | .append xs => .append <$> xs.mapM (·.export)
      | .trace cls msg children c =>
        let msg ← msg.export
        let children ← children.mapM (·.export)
        pure (.trace cls msg children c)
      | .term hl => .term <$> hl.export
      | .goal g => .goal <$> g.export
    if let some k := (← get).messageContentsKeys.get? txt then
      return k
    else
      modifyGet fun e =>
        let k := e.nextKey
        (k,
          { e with
            nextKey := k + 1,
            messageContents := e.messageContents.insert k txt,
            messageContentsKeys := e.messageContentsKeys.insert txt k })

  partial def Highlighted.export (hl : Highlighted) : ExportM Export.Key := do
    let hl : Export.Highlighted ←
      match hl with
      | .text s => pure (Export.Highlighted.text s)
      | .unparsed s => pure (Export.Highlighted.unparsed s)
      | .point k i => .point k <$> i.export
      | .tactics info s e hl => do
        pure <| .tactics (← info.mapM (·.export)) s e (← hl.export)
      | .span i hl => do
        pure <| .span (← i.mapM fun ⟨k, txt⟩ => do return ⟨k, (← txt.export)⟩) (← hl.export)
      | .seq hls => .seq <$> hls.mapM (·.export)
      | .token tok => .token <$> tok.export
    if let some k := (← get).codeKeys.get? hl then
      return k
    else
      modifyGet fun e =>
        let k := e.nextKey
        (k,
          { e with
            nextKey := k + 1,
            code := e.code.insert k hl,
            codeKeys := e.codeKeys.insert hl k })

  partial def Highlighted.Hypothesis.export (hyp : Highlighted.Hypothesis Highlighted) : ExportM Export.Hypothesis := do
    return { names := (← hyp.names.mapM (·.export)), typeAndVal := (← hyp.typeAndVal.export) }

  partial def Highlighted.Goal.export (goal : Highlighted.Goal Highlighted) : ExportM Export.Key := do
    let goal : Export.Goal := { goal with
      hypotheses := (← goal.hypotheses.mapM (·.export)),
      conclusion := (← goal.conclusion.export)
    }
    if let some k := (← get).goalKeys.get? goal then
      return k
    else
      modifyGet fun e =>
        let k := e.nextKey
        (k,
          { e with
            nextKey := k + 1,
            goals := e.goals.insert k goal,
            goalKeys := e.goalKeys.insert goal k })
end


mutual
  partial def Export.toToken (data : Export) (key : Key) : Except String Highlighting.Token := do
    let some tok := data.tokens.get? key
      | throw s!"Not found: token at key {key}"
    pure tok

  partial def Export.toMessageContents (data : Export) (key : Key) : Except String (Highlighted.MessageContents Highlighting.Highlighted) := do
    let some txt := data.messageContents.get? key
      | throw s!"Not found: message contents at key {key}"
    match txt with
    | .text s => return .text s
    | .append txts => .append <$> txts.mapM data.toMessageContents
    | .trace cls msg children collapsed => do
      return .trace cls (← data.toMessageContents msg) (← children.mapM data.toMessageContents) collapsed
    | .term e => .term <$> data.toHighlighted e
    | .goal g => .goal <$> data.toGoal g

  partial def Export.toGoal (data : Export) (key : Key) : Except String (Highlighted.Goal Highlighting.Highlighted) := do
    let some g := data.goals.get? key
      | throw s!"Not found: goal at key {key}"
    let hypotheses : Array (Highlighted.Hypothesis Highlighting.Highlighted) ← g.hypotheses.mapM fun {names, typeAndVal} => do
      return {names := (← names.mapM data.toToken), typeAndVal := (← data.toHighlighted typeAndVal)}
    let conclusion ← data.toHighlighted g.conclusion
    return {g with hypotheses, conclusion}

  partial def Export.toHighlighted (data : Export) (key : Key) : Except String Highlighting.Highlighted := do
    let some hl := data.code.get? key
      | throw s!"Not found: highlighted code at key {key}"
    match hl with
    | .token tok => .token <$> data.toToken tok
    | .unparsed s => return .unparsed s
    | .text s => return .text s
    | .point k i => .point k <$> data.toMessageContents i
    | .tactics info s e hl => do
      return .tactics (← info.mapM data.toGoal) s e (← data.toHighlighted hl)
    | .span i hl => do
      return .span (← i.mapM fun ⟨k, txt⟩ => do return ⟨k, (← data.toMessageContents txt)⟩) (← data.toHighlighted hl)
    | .seq hls => .seq <$> hls.mapM data.toHighlighted
end

def ExportCode.toHighlighted (data : ExportCode) : Except String Highlighting.Highlighted :=
  data.toExport.toHighlighted data.top

def Highlighted.exportCode (hl : Highlighting.Highlighted) : ExportCode :=
  let (top, state) := hl.export.run {}
  {state with top}
