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
  | sort (doc? : Option String)
  | levelVar (name : Name)
  /-- A level operator, such as "+" or "imax" -/
  | levelOp (which : String)
  | levelConst (i : Nat)
  | moduleName (name : Name)
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
    | .sort doc? => mkCApp ``sort #[quote doc?]
    | .levelVar n => mkCApp ``levelVar #[quote n]
    | .levelConst v => mkCApp ``levelConst #[quote v]
    | .moduleName m => mkCApp ``moduleName #[quote m]
    | .levelOp n => mkCApp ``levelOp #[quote n]
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

structure Highlighted.Hypothesis (expr : Type) where
  names : Array Token
  typeAndVal : expr
deriving Repr, BEq, Hashable, ToJson, FromJson

def Highlighted.Hypothesis.map (f : α → β) (h : Hypothesis α) : Hypothesis β :=
  { h with typeAndVal := f h.typeAndVal }

structure Highlighted.Goal (expr : Type) where
  name : Option String
  goalPrefix : String
  hypotheses : Array (Hypothesis expr)
  conclusion : expr
deriving Repr, BEq, Hashable, ToJson, FromJson

def Highlighted.Goal.map (f : α → β) (g : Goal α) : Goal β :=
  { g with
    hypotheses := g.hypotheses.map (·.map f)
    conclusion := f g.conclusion }

instance [Quote expr] : Quote (Highlighted.Hypothesis expr) where
  quote
    | {names, typeAndVal} =>
      Syntax.mkCApp ``Highlighted.Hypothesis.mk #[quote names, quote typeAndVal]

instance [Quote expr] : Quote (Highlighted.Goal expr) where
  quote
    | {name, goalPrefix, hypotheses, conclusion} =>
      Syntax.mkCApp ``Highlighted.Goal.mk #[quote name, quote goalPrefix, quote hypotheses, quote conclusion]

inductive Highlighted.Span.Kind where
  | error
  | warning
  | info
deriving Repr, DecidableEq, Inhabited, BEq, Hashable

instance : ToJson Highlighted.Span.Kind where
  toJson
    | .error => "error"
    | .warning => "warning"
    | .info => "info"

instance : FromJson Highlighted.Span.Kind where
  fromJson?
    | .str "error" => pure .error
    | .str "warning" => pure .warning
    | .str "info" => pure .info
    | other => throw s!"For Highlighted.Span.Kind, expected \"error\", \"warning\", or \"info\", but got {other.compress}"

def Highlighted.Span.Kind.toString : Highlighted.Span.Kind → String
  | .error => "error"
  | .warning => "warning"
  | .info => "info"

def Highlighted.Span.Kind.ofSeverity : MessageSeverity → Highlighted.Span.Kind
  | .error => .error
  | .warning => .warning
  | .information => .info

def Highlighted.Span.Kind.toSeverity : Highlighted.Span.Kind → MessageSeverity
  | .error => .error
  | .warning => .warning
  | .info => .information

instance : ToString Highlighted.Span.Kind where
  toString := Highlighted.Span.Kind.toString

open Highlighted Span Kind in
open Syntax in
instance : Quote Kind where
  quote
    | .error => mkCApp ``error #[]
    | .warning => mkCApp ``warning #[]
    | .info => mkCApp ``info #[]

/-- A first-order, context-independent, fixed-width approximation of `MessageData` -/
inductive Highlighted.MessageContents (expr) where
  | text : String → MessageContents expr
  | goal : Goal expr → MessageContents expr
  | term : expr → MessageContents expr
  | trace (cls : Name) (msg : MessageContents expr) (children : Array (MessageContents expr)) (collapsed : Bool) : MessageContents expr
  | append : Array (MessageContents expr) → MessageContents expr
deriving Repr, Inhabited, BEq, Hashable, ToJson, FromJson

open Highlighted MessageContents in
open Syntax in
partial instance [Quote expr] : Quote (MessageContents expr) where
  quote := q
where
  q
    | .text s => mkCApp ``text #[quote s]
    | .goal g => mkCApp ``goal #[quote g]
    | .term e => mkCApp ``term #[quote e]
    | .trace cls msg children collapsed =>
      have : Quote (MessageContents expr) := ⟨q⟩
      mkCApp ``MessageContents.trace #[quote cls, q msg, quote children, quote collapsed]
    | .append ms =>
      have : Quote (MessageContents expr) := ⟨q⟩
      mkCApp ``append #[quote ms]

open Highlighted in
inductive Highlighted where
  | token (tok : Token)
  | text (str : String)
  | seq (highlights : Array Highlighted)
  | span (info : Array (Span.Kind × MessageContents Highlighted)) (content : Highlighted)
  | tactics (info : Array (Goal Highlighted)) (startPos : Nat) (endPos : Nat) (content : Highlighted)
  | point (kind : Span.Kind) (info : MessageContents Highlighted)
  | unparsed (str : String)
deriving Repr, Inhabited, BEq, Hashable, ToJson, FromJson

structure Highlighted.Message where
  severity : Span.Kind
  contents : MessageContents Highlighted
deriving Repr, Inhabited, BEq, Hashable, ToJson, FromJson

/-- Constructs a message without any “live” elements from a string and a severity -/
def Highlighted.Message.ofSeverityString (sev : MessageSeverity) (contents : String) : Highlighted.Message where
  severity := .ofSeverity sev
  contents := .text contents

def Highlighted.empty : Highlighted := .seq #[]

/--
Checks whether the highlighted code would render as the empty string with no metadata.
-/
partial def Highlighted.isEmpty : Highlighted → Bool
  | .text s => s.isEmpty
  | .seq xs => xs.all isEmpty
  | _ => false

/--
Appends two pieces of highlighted code, applying some simplifications and merging adjacent info
regions.
-/
partial def Highlighted.append (hl1 hl2 : Highlighted) : Highlighted :=
  if hl1.isEmpty then hl2
  else if hl2.isEmpty then hl1
  else match hl1, hl2 with
  | .text str1, .text str2 => .text (str1 ++ str2)
  | .seq _, .seq ys =>
    ys.foldl (init := hl1) Highlighted.append
  | .seq xs, x => .seq (pushHl xs x)
  | x, .seq xs =>
    xs.foldl (init := x) Highlighted.append
  | x, y => .seq #[x, y]
where
  -- Merge subsequent info regions. This is necessary when highlighted code has been split (e.g.
  -- into lines), processed, and is then recombined.
  pushHl (xs : Array Highlighted) (x : Highlighted) : Array Highlighted :=
    if xs.size > 0 then
      let last := Compat.Array.back! xs
      let last' :=
        match last, x with
        | .tactics i1 s1 e1 inner1, .tactics i2 s2 e2 inner2 =>
          if i1 == i2 && s1 == s2 && e1 == e2 then #[.tactics i1 s1 e1 (inner1.append inner2)]
          else #[last, x]
        | .span i1 inner1, .span i2 inner2 =>
          if i1 == i2 then #[.span i1 (inner1.append inner2)]
          else #[last, x]
        | .text s1, .text s2 => #[.text (s1 ++ s2)]
        | _, _ => #[last, x]
      xs.extract 0 (xs.size - 1) ++ last'
    else
      #[x]

instance : Append Highlighted where
  append := Highlighted.append

/--
Extracts all names that are marked as definition sites.
-/
partial def Highlighted.definedNames : Highlighted → NameSet
  | .token ⟨tok, _⟩ =>
    match tok with
    | .const n _ _ true => NameSet.empty.insert n
    | _ => {}
  | .span _ hl | .tactics _ _ _ hl => hl.definedNames
  | .seq hls => hls.map (·.definedNames) |>.foldr Compat.NameSet.union {}
  | .text .. | .point .. | .unparsed .. => {}

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

/--
Simplifies the internal structure of highlighted code as follows:
 1. Nested `seq`s are flattened
 2. Adjacent `text`s and `seq`s are merged
 3. Empty nodes are removed
-/
partial def Highlighted.simplifyInternals : (hl : Highlighted) → Highlighted
  | .seq xs => xs.map simplifyInternals |>.foldl (init := .empty) .append
  | hl@(.point ..) => hl
  | .tactics x y z m => .tactics x y z (simplifyInternals m)
  | .span x y => .span x (simplifyInternals y)
  | .text "" => .empty
  | .text s => .text s
  | .token t => .token t
  | .unparsed s => .unparsed s

instance : ToJson Highlighted where
  toJson hl :=
    -- Get the derived instance, and call it on the simplified data
    let ⟨toJson'⟩ := inferInstanceAs (ToJson Highlighted)
    toJson' hl.simplifyInternals

open Lean Syntax in
open Highlighted in
partial instance : Quote Highlighted where
 quote hl := quote' hl.simplifyInternals
where
  quote'
    | .token tok => mkCApp ``token #[quote tok]
    | .text str => mkCApp ``text #[quote str]
    | .seq hls => quoteSeq hls
    | .span info content =>
      have : Quote Highlighted := ⟨quote'⟩
      mkCApp ``span #[quote info, quote' content]
    | .tactics info startPos endPos content =>
      have : Quote Highlighted := ⟨quote'⟩
      mkCApp ``tactics #[quote info, quote startPos, quote endPos, quote' content]
    | .point k info =>
      have : Quote Highlighted := ⟨quote'⟩
      mkCApp ``point #[quote k, quote info]
    | .unparsed str => mkCApp ``unparsed #[quote str]

  quoteSeq (xs : Array Highlighted) : Term :=
    if xs.size ≤ 10 then
      mkCApp (`SubVerso.Highlighting.Highlighted ++ s!"seq{xs.size}".toName) (xs.map quote')
    else
      let n := xs.size / 2
      let pre := xs.extract 0 n
      let post := xs.extract n xs.size
      mkCApp ``Highlighted.append #[quoteSeq pre, quoteSeq post]

open Highlighted in
open Syntax in
instance : Quote Highlighted.Message where
  quote
    | ⟨severity, contents⟩ => mkCApp ``Highlighted.Message.mk #[quote severity, quote contents]

namespace Highlighted

/--
Converts highlighted code to a string.
-/
partial def toString : Highlighted → String
  | .seq xs => xs.foldl (init := "") (fun s hl => s ++ hl.toString)
  | .point .. => ""
  | .tactics _ _ _ x | .span _ x => x.toString
  | .text s | .token ⟨_, s⟩ | .unparsed s => s

/--
Converts highlighted code to a string, stopping when the provided length is reached
-/
partial def toStringPrefix (n : Nat) (hl : Highlighted) : String := Id.run do
  let mut n := n
  let mut todo := [hl]
  let mut str := ""
  while n > 0 do
    match todo with
    | [] => break
    | .point .. :: more => todo := more
    | .tactics _ _ _ x :: more | .span _ x :: more => todo := x :: more
    | .seq xs :: more => todo := xs.toList ++ more
    | .text s :: more | .token ⟨_, s⟩ :: more | .unparsed s :: more =>
      todo := more
      str := str ++ s
      n := n - s.length
  return str

/--
Converts highlighted code to a string from the right, stopping when the provided length is reached.
-/
def toStringSuffix (n : Nat) (hl : Highlighted) : String := Id.run do
  let mut n := n
  let mut todo := #[hl]
  let mut str := ""
  while n > 0 do
    match todo.back? with
    | none => break
    | some hl =>
      todo := todo.pop
      match hl with
      | .point .. => pure ()
      | .tactics _ _ _ x | .span _ x => todo := todo.push x
      | .seq xs  => todo := todo ++ xs
      | .text s | .token ⟨_, s⟩ | .unparsed s =>
        str := s ++ str
        n := n - s.length
  return str

/--
Converts highlighted code to a string from the right, stopping when a character that doesn't satisfy `p` is reached.
-/
def takeStringRightWhile (hl : Highlighted) (p : Char → Bool) : String := Id.run do
  let mut todo := #[hl]
  let mut str := ""
  repeat
    match todo.back? with
    | none => break
    | some hl =>
      todo := todo.pop
      match hl with
      | .point .. => pure ()
      | .tactics _ _ _ x | .span _ x => todo := todo.push x
      | .seq xs  => todo := todo ++ xs
      | .text s | .token ⟨_, s⟩ | .unparsed s =>
        let s' := s.takeRightWhile p
        str := s' ++ str
        if s' != s then return str
  return str

/--
Removes the first `n` characters of the leading `text` content, stopping if some other content is
encountered, even metadata.
-/
def dropText (n : Nat) (hl : Highlighted) : Highlighted := Id.run do
  let mut n := n
  let mut todo := [hl]
  let mut out : Highlighted := .empty
  while n > 0 do
    match todo with
    | [] => break
    | hl@(.point ..) :: more | hl@(.tactics ..) :: more | hl@(.span ..) :: more  | hl@(.token ..) :: more | hl@(.unparsed ..) :: more =>
      out := out ++ hl
      for hl' in more do out := out ++ hl'
      return out
    | .seq xs :: more =>
      todo := xs.toList ++ more
    | .text s :: more =>
      todo := more
      if n ≤ s.length then
        if n < s.length then
          out := out ++ .text (s.drop n)
        for hl' in more do out := out ++ hl'
        return out
      else
        n := n - s.length
  return out

/--
Removes the last `n` characters of the leading `text` content, stopping if some other content is
encountered, even metadata.
-/
def dropTextRight (n : Nat) (hl : Highlighted) : Highlighted := Id.run do
  let mut n := n
  let mut todo := #[hl]
  while n > 0 do
    match todo.back? with
    | none => break
    | some hl =>
      match hl with
      | .point .. | .tactics .. | .span .. | .token .. | .unparsed .. =>
        return .seq todo
      | .seq xs =>
        todo := todo.pop ++ xs
      | .text s =>
        todo := todo.pop
        if n < s.length then
          return .seq todo ++ .text (s.dropRight n)
        else if n = s.length then
          return .seq todo
        else
          n := n - s.length
  -- If the loop terminates then we ran out of code before running out of Nat
  return .seq todo

/--
Keep at least `n` characters of the original source.
-/
partial def take (n : Nat) (hl : Highlighted) : Highlighted := Id.run do
  let mut n := n
  let mut todo := [hl]
  let mut out : Highlighted := .empty
  while n > 0 do
    match todo with
    | [] => break
    | hl@(.point ..) :: more =>
      out := out ++ hl
      todo := more
    | hl@(.tactics _ _ _ _) :: more | hl@(.span _ _) :: more =>
      out := out ++ hl
      n := n - hl.toString.length
      todo := more
    | .seq xs :: more =>
      todo := xs.toList ++ more
    | hl@(.text s) :: more | hl@(.token ⟨_, s⟩) :: more | hl@(.unparsed s) :: more =>
      todo := more
      out := out ++ hl
      n := n - s.length
  return out

/--
Converts a goal to a string.

No pretty-printing is performed, so this is mostly useful for internal tests and expected output,
rather than display to readers.
-/
partial def Goal.toString : Highlighted.Goal Highlighted → String
  | {name, goalPrefix, hypotheses, conclusion} =>
    (name.map ("case " ++ · ++ "\n") |>.getD "") ++
    ((hypotheses.map hString) |>.toList |> String.join) ++
    goalPrefix ++
    conclusion.toString
where hString
  | ⟨xs, t⟩ =>
    let names := xs.map (fun tok => Highlighted.token tok |>.toString) |>.toList
    let names := " ".intercalate names
    s!"{names} : {t.toString}\n"

partial def MessageContents.toString (expandTraces : List Name := []) : MessageContents Highlighted → String
  | .trace cls msg children collapsed =>
    let collapsed := collapsed && !(expandTraces.contains cls)
    let parent := s!"[{cls}] {msg.toString expandTraces}"
    if collapsed then parent ++ "\n"
    else
      children.foldl (init := parent ++ "\n") (fun acc ch => acc ++ (indentString (ch.toString expandTraces)))
  | .goal g => g.toString
  | .append xs => xs.foldl (init := "") (fun str msg => str ++ msg.toString expandTraces)
  | .term hl => hl.toString
  | .text s => s
where
  indentString (s : String) : String :=
    "\n".intercalate <| s.splitOn "\n" |>.map (fun l => if l.any (!·.isWhitespace) then "  " ++ l else l)

/--
Truncates a message to textual content at the beginning, inclusive.
-/
partial def MessageContents.startAt (pattern : String) (txt : MessageContents expr) : Option (MessageContents expr) := do
  let mut todo := [txt]
  let mut pat := pattern
  let mut strict : Bool := false

  while !todo.isEmpty do
    match todo with
    | [] => break
    | .trace .. :: todo' | .goal .. :: todo' | .term .. :: todo' => todo := todo'
    | .text s :: todo' =>
      if strict then
        if s.startsWith (pat.take s.length) then
          let s' := s.drop pat.length
          if s'.isEmpty then
            pat := pat.drop s.length
            todo := todo'
          else
            return .append (.text (pattern ++ s') :: todo').toArray
        else failure
      else if let some (startFrom', s') := prefixMatch pat s then
        if s'.isEmpty then
          pat := startFrom'
          todo := todo'
        else
          return .append (.text (pattern ++ s') :: todo').toArray
      else
        todo := todo'
    | .append xs :: todo' =>
      todo := xs.toList ++ todo'

  failure
where
  prefixMatch (needle haystack : String) : Option (String × String) := do
    let mut haystack := haystack

    while !haystack.isEmpty do
      let pat := needle.take haystack.length
      if haystack.startsWith pat then
        return (needle.drop pat.length, haystack.drop pat.length)
      haystack := haystack.drop 1
    failure

/--
Truncates a message to textual content at the end, inclusive.
-/
partial def MessageContents.stopAt (pattern : String) (txt : MessageContents expr) : Option (MessageContents expr) := do
  let mut todo := [txt]
  let mut pat := pattern
  let mut strict : Bool := false

  while !todo.isEmpty do
    match todo with
    | [] => break
    | .trace .. :: todo' | .goal .. :: todo' | .term .. :: todo' => todo := todo'
    | .text s :: todo' =>
      if strict then
        if s.endsWith (pat.takeRight s.length) then
          let s' := s.dropRight pat.length
          if s'.isEmpty then
            pat := pat.dropRight s.length
            todo := todo'
          else
            return .append (.text (s' ++ pattern) :: todo').toArray.reverse
        else failure
      else if let some (endAt', s') := suffixMatch pat s then
        if s'.isEmpty then
          pat := endAt'
          todo := todo'
        else
          return .append (.text (s' ++ pattern) :: todo').toArray.reverse
      else
        todo := todo'
    | .append xs :: todo' =>
      todo := xs.reverse.toList ++ todo'

  failure
where
  suffixMatch (needle haystack : String) : Option (String × String) := do
    let mut haystack := haystack

    while !haystack.isEmpty do
      let pat := needle.takeRight haystack.length
      if haystack.endsWith pat then
        return (needle.dropRight pat.length, haystack.dropRight pat.length)
      haystack := haystack.dropRight 1
    failure

/--
Truncates a message to textual content at the beginning, inclusive.
-/
def Message.startAt (pat : String) (msg : Message) : Option Message := do
  msg.contents.startAt pat |>.map ({msg with contents := ·})

/--
Truncates a message to textual content at the end, inclusive.
-/
def Message.stopAt (pat : String) (msg : Message) : Option Message := do
  msg.contents.stopAt pat |>.map ({msg with contents := ·})


def Message.toString (expandTraces : List Name := []) (message : Message) : String :=
  message.contents.toString (expandTraces := expandTraces)

private def minIndentString (str : String) : Nat :=
  let indents := str.split (· == '\n') |>.filterMap fun line =>
    if line.all (· == ' ') then none
    else some (line.takeWhile (· == ' ') |>.length)
  indents.min?.getD 0

/--
Returns the minimal indentation of any non-whitespace line of code.
-/
def indentation (hl : Highlighted) : Nat := Id.run do
  minIndentString hl.toString

/--
Adds `howMuch` spaces after each newline.
-/
partial def indent (hl : Highlighted) (howMuch : Nat := 2) : Highlighted :=
  let i := "\n".pushn ' ' howMuch
  match hl with
  | .seq hls => .seq (hls.map (·.indent howMuch))
  | .unparsed str => .unparsed (str.replace "\n" i)
  | .text str => .text (str.replace "\n" i)
  | .tactics info s e hl => .tactics info s e (hl.indent howMuch)
  | .span info hl => .span info (hl.indent howMuch)
  | .point .. | .token .. => hl
