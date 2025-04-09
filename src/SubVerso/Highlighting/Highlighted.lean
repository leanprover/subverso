/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Data.Json
import Lean.Expr
import Lean.SubExpr -- for the To/FromJSON FVarId instances
import SubVerso.Compat

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

private local instance nameToJson : ToJson Name := ⟨altNameJson⟩
private local instance nameFromJson : FromJson Name := ⟨altNameUnJson⟩

private partial local instance : ToJson Level where
  toJson := go
where
  go
    | .zero => .arr #["zero"]
    | .succ l => .arr #["succ", go l]
    | .param n => .arr #["param", nameToJson.toJson n]
    | .max l l' => .arr #["max", go l, go l']
    | .imax l l' => .arr #["imax", go l, go l']
    | .mvar ⟨m⟩ => .arr #["mvar", nameToJson.toJson m]

private partial local instance : FromJson Level where
  fromJson? v := go v
where
  go
    | .arr #["zero"] => pure .zero
    | .arr #["succ", l] => .succ <$> go l
    | .arr #["param", n] => .param <$> nameFromJson.fromJson? n
    | .arr #["max", l, l'] => .max <$> go l <*> go l'
    | .arr #["imax", l, l'] => .imax <$> go l <*> go l'
    | .arr #["mvar", m] => (.mvar ⟨·⟩) <$> nameFromJson.fromJson? m
    | other => throw s!"Failed to decode {other} as a level"

inductive Token.Kind where
  | /-- `occurrence` is a unique identifier that unites the various keyword tokens from a given production -/
    keyword (name : Option Name) (occurrence : Option String) (docs : Option String)
  | const (name : Name) (signature : String) (docs : Option String) (isDef : Bool)
  | anonCtor (name : Name) (signature : String) (docs : Option String)
  | var (name : FVarId) (type : String)
  | str (string : String)
  | option (name : Name) (declName : Name) (docs : Option String)
  | docComment
  | sort (level : Level) (doc? : Option String)
  | /-- The token represents some otherwise-undescribed Expr whose type is known -/
    withType (type : String)
  | unknown
deriving Repr, Inhabited, BEq, Hashable, ToJson, FromJson

open Lean.Syntax in
instance : Quote LevelMVarId where
  quote | ⟨m⟩ => mkCApp ``LevelMVarId.mk #[quote m]

open Lean.Syntax in
private partial def quoteLevel : Level → Term
  | .zero => mkCApp ``Level.zero #[]
  | .succ l => mkCApp ``Level.succ #[quoteLevel l]
  | .param n => mkCApp ``Level.param #[quote n]
  | .max l l' => mkCApp ``Level.max #[quoteLevel l, quoteLevel l']
  | .imax l l' => mkCApp ``Level.imax #[quoteLevel l, quoteLevel l']
  | .mvar mv => mkCApp ``Level.mvar #[quote mv]

instance : Quote Level := ⟨quoteLevel⟩

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
    | .sort l doc? => mkCApp ``sort #[quote l, quote doc?]
    | .withType t => mkCApp ``withType #[quote t]
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

def Highlighted.append : Highlighted → Highlighted → Highlighted
  | .text str1, .text str2 => .text (str1 ++ str2)
  | .seq xs, .seq ys => .seq (xs ++ ys)
  | .seq xs,  x => .seq (xs ++ #[x])
  | x, .seq xs => .seq (#[x] ++ xs)
  | x, y => .seq #[x, y]

instance : Append Highlighted where
  append := Highlighted.append

partial def Highlighted.definedNames : Highlighted → NameSet
  | .token ⟨tok, _⟩ =>
    match tok with
    | .const n _ _ true => NameSet.empty.insert n
    | _ => {}
  | .span _ hl | .tactics _ _ _ hl => hl.definedNames
  | .seq hls => hls.map (·.definedNames) |>.foldr Compat.NameSet.union {}
  | .text .. | .point .. => {}

def Highlighted.seq0 : Highlighted := .seq #[]
def Highlighted.seq1 (x0 : Highlighted) : Highlighted := .seq #[x0]
def Highlighted.seq2 (x0 x1 : Highlighted) : Highlighted := .seq #[x0, x1]
def Highlighted.seq3 (x0 x1 x2 : Highlighted) : Highlighted := .seq #[x0, x1, x2]
def Highlighted.seq4 (x0 x1 x2 x3 : Highlighted) : Highlighted := .seq #[x0, x1, x2, x3]
def Highlighted.seq5 (x0 x1 x2 x3 x4 : Highlighted) : Highlighted := .seq #[x0, x1, x2, x3, x4]
def Highlighted.seq6 (x0 x1 x2 x3 x4 x5 : Highlighted) : Highlighted := .seq #[x0, x1, x2, x3, x4, x5]
def Highlighted.seq7 (x0 x1 x2 x3 x4 x5 x6 : Highlighted) : Highlighted := .seq #[x0, x1, x2, x3, x4, x5, x6]
def Highlighted.seq8 (x0 x1 x2 x3 x4 x5 x6 x7 : Highlighted) : Highlighted := .seq #[x0, x1, x2, x3, x4, x5, x6, x7]
def Highlighted.seq9 (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Highlighted) : Highlighted := .seq #[x0, x1, x2, x3, x4, x5, x6, x7, x8]
def Highlighted.seq10 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Highlighted) : Highlighted := .seq #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9]

/-- Makes highlighted code quote into smaller terms -/
partial def Highlighted.compress : Highlighted → Highlighted
  | .seq xs =>
    xs.map (·.compress) |>.foldl (init := .seq #[]) (· ++ ·)
  | .span info content => .span info content.compress
  | .tactics info s e content => .tactics info s e content.compress
  | t => t

open Lean Syntax in
open Highlighted in
partial instance : Quote Highlighted where
 quote hl := quote' (compress hl)
where
  quote'
    | .token tok => mkCApp ``token #[quote tok]
    | .text str => mkCApp ``text #[quote str]
    | .seq hls => quoteSeq hls
    | .span info content => mkCApp ``span #[quote info, quote' content]
    | .tactics info startPos endPos content =>
      have : Quote Highlighted := ⟨quote'⟩
      mkCApp ``tactics #[quote info, quote startPos, quote endPos, quote' content]
    | .point k info => mkCApp ``point #[quote k, quote info]

  quoteSeq (xs : Array Highlighted) : Term :=
    if xs.size ≤ 10 then
      mkCApp (`SubVerso.Highlighting.Highlighted ++ s!"seq{xs.size}".toName) (xs.map quote')
    else
      let n := xs.size / 2
      let pre := xs.extract 0 n
      let post := xs.extract n xs.size
      mkCApp ``Highlighted.append #[quoteSeq pre, quoteSeq post]
