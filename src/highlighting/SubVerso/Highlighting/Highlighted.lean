/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Data.Json
import Lean.Expr
import Lean.SubExpr -- for the To/FromJSON FVarId instances

open Lean

namespace SubVerso.Highlighting

deriving instance Repr for Std.Format.FlattenBehavior
deriving instance Repr for Std.Format

-- Workaround for the fact that the default From/ToJson instances for Name
-- don't always round-trip

private def altNameJson (n : Name) : Json := Json.arr (splitName #[] n)
where
  splitName acc
    | .anonymous => acc
    | .num x n => splitName acc x |>.push n
    | .str x s => splitName acc x |>.push s

private def altNameUnJson (json : Json) : Except String Name := do
  let arr ← json.getArr?
  let mut n := .anonymous
  for v in arr do
    match v with
    | (s : String) => n := n.str s
    | (i : Nat) => n := n.num i
    | other => .error s!"Expected a string or number as a name component, got '{other}'"
  pure n

private local instance : ToJson Name := ⟨altNameJson⟩
private local instance : FromJson Name := ⟨altNameUnJson⟩


inductive Token.Kind where
  | /-- `occurrence` is a unique identifier that unites the various keyword tokens from a given production -/
    keyword (name : Option Name) (occurrence : Option String) (docs : Option String)
  | const (name : Name) (signature : String) (docs : Option String) (isDef : Bool)
  | anonCtor (name : Name) (signature : String) (docs : Option String)
  | var (name : FVarId) (type : String)
  | str (string : String)
  | option (name : Name) (declName : Name) (docs : Option String)
  | docComment
  | sort
  | unknown
deriving Repr, Inhabited, BEq, Hashable, ToJson, FromJson

open Token.Kind in
open Syntax (mkCApp) in
instance : Quote Token.Kind where
  quote
    | .keyword n occ docs => mkCApp ``keyword #[quote n, quote occ, quote docs]
    | .const n sig docs isDef => mkCApp ``const #[quote n, quote sig, quote docs, quote isDef]
    | .anonCtor n sig docs => mkCApp ``anonCtor #[quote n, quote sig, quote docs]
    | .option n d docs => mkCApp ``option #[quote n, quote d, quote docs]
    | .var (.mk n) type => mkCApp ``var #[mkCApp ``FVarId.mk #[quote n], quote type]
    | .str s => mkCApp ``str #[quote s]
    | .docComment => mkCApp ``docComment #[]
    | .sort => mkCApp ``sort #[]
    | .unknown => mkCApp ``unknown #[]

structure Token where
  kind : Token.Kind
  content : String
deriving Repr, Inhabited, BEq, Hashable, ToJson, FromJson

open Syntax in
instance : Quote Token where
  quote
    | (.mk kind content) =>
      mkCApp ``Token.mk #[quote kind, quote content]

structure Highlighted.Goal (expr) where
  name : Option Name
  goalPrefix : String
  hypotheses : Array (Name × Token.Kind × expr)
  conclusion : expr
deriving Repr, BEq, Hashable, ToJson, FromJson

def Highlighted.Goal.map (f : α → β) (g : Goal α) : Goal β :=
  {g with
    hypotheses := g.hypotheses.map (fun (x, k, e) => (x, k, f e))
    conclusion := f g.conclusion}

instance [Quote expr] : Quote (Highlighted.Goal expr) where
  quote
    | {name, goalPrefix, hypotheses, conclusion} =>
      Syntax.mkCApp ``Highlighted.Goal.mk #[quote name, quote goalPrefix, quote hypotheses, quote conclusion]


inductive Highlighted.Span.Kind where
  | error
  | warning
  | info
deriving Repr, DecidableEq, Inhabited, BEq, Hashable, ToJson, FromJson

open Highlighted Span Kind in
open Syntax in
instance : Quote Kind where
  quote
    | .error => mkCApp ``error #[]
    | .warning => mkCApp ``warning #[]
    | .info => mkCApp ``info #[]

inductive Highlighted where
  | token (tok : Token)
  | text (str : String)
  | seq (highlights : Array Highlighted)
  -- TODO replace messages as strings with structured info
  | span (info : Array (Highlighted.Span.Kind × String)) (content : Highlighted)

  | tactics (info : Array (Highlighted.Goal Highlighted)) (startPos : Nat) (endPos : Nat) (content : Highlighted)
  | point (kind : Highlighted.Span.Kind) (info : String)
deriving Repr, Inhabited, BEq, Hashable, ToJson, FromJson

def Highlighted.empty : Highlighted := .seq #[]

instance : Append Highlighted where
  append
    | .text str1, .text str2 => .text (str1 ++ str2)
    | .seq xs, .seq ys => .seq (xs ++ ys)
    | .seq xs,  x => .seq (xs ++ #[x])
    | x, .seq xs => .seq (#[x] ++ xs)
    | x, y => .seq #[x, y]

partial def Highlighted.definedNames : Highlighted → NameSet
  | .token ⟨tok, _⟩ =>
    match tok with
    | .const n _ _ true => NameSet.empty.insert n
    | _ => {}
  | .span _ hl | .tactics _ _ _ hl => hl.definedNames
  | .seq hls => hls.map (·.definedNames) |>.foldr NameSet.append {}
  | .text .. | .point .. => {}

open Lean Syntax in
open Highlighted in
partial instance : Quote Highlighted where
 quote := quote'
where
  quoteArray {α : _} (_inst : Quote α) (xs : Array α) : TSyntax `term :=
    mkCApp ``List.toArray #[quote xs.toList]

  quoteHl {α} [Quote α] : Quote (Goal α) := inferInstance

  quote'
    | .token tok => mkCApp ``token #[quote tok]
    | .text str => mkCApp ``text #[quote str]
    | .seq hls => mkCApp ``seq #[quoteArray ⟨quote'⟩ hls]
    | .span info content => mkCApp ``span #[quote info, quote' content]
    | .tactics info startPos endPos content =>
      mkCApp ``tactics #[quoteArray (@quoteHl _ ⟨quote'⟩) info, quote startPos, quote endPos, quote' content]
    | .point k info => mkCApp ``point #[quote k, quote info]
