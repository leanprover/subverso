/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Widget.InteractiveCode
import Lean.Widget.TaggedText


import SubVerso.Compat
import SubVerso.Highlighting.Highlighted

open Lean hiding HashMap
open Elab
open Lean.Widget (TaggedText)
open Lean.Widget
open Lean.PrettyPrinter (InfoPerPos)
open SubVerso.Compat (HashMap)

initialize registerTraceClass `SubVerso.Highlighting.Code

namespace SubVerso.Highlighting

partial def Token.Kind.priority : Token.Kind → Nat
  | .var .. => 2
  | .str .. => 3
  | .const .. => 5
  | .option .. => 4
  | .sort => 4
  | .keyword _ _ _ => 3
  | .docComment => 1
  | .unknown => 0

-- Find all info nodes whose canonical span matches the given syntax
def infoForSyntax (t : InfoTree) (stx : Syntax) : List (ContextInfo × Info) :=
  t.collectNodesBottomUp fun ci info _ soFar =>
    if info.stx.getPos? true == stx.getPos? true &&
       info.stx.getTailPos? true == stx.getTailPos? true then
      (ci, info) :: soFar
    else soFar

-- Find the nodes whose canonical span includes the given syntax
def infoIncludingSyntax (t : InfoTree) (stx : Syntax) : List (ContextInfo × Info) :=
  t.collectNodesBottomUp fun ci info _ soFar =>
    if let some true := do
      let start ← info.stx.getPos? true
      let start' ← stx.getPos? true
      let stop ← info.stx.getTailPos? true
      let stop' ← stx.getTailPos? true
      pure <| start ≤ start' && stop ≥ stop'
    then
      (ci, info) :: soFar
    else soFar



partial def bestD (sems : Array Token.Kind) (default : Token.Kind) : Token.Kind :=
  if let some m := sems.back? then
    bestD sems.pop <| if m.priority > default.priority then m else default
  else
    default

def fakeToken (meaning : Token.Kind) (tok : String) : Token where
  content := tok
  kind := meaning


namespace UnionFind
structure State (α : Type u) where
  contents : Array (Nat ⊕ (α × Nat)) := {}
  [eq : BEq α]
  [hashable : Hashable α]
  indices : HashMap α Nat := {}

def State.init [BEq α] [Hashable α] : State α := {}

def insert [Monad m] [MonadState (State α) m] [BEq α] [Hashable α] (x : α) : m Nat := do
  if let some i := (← get).indices[x]? then
    pure i
  else
    let i := (← get).contents.size
    modify fun s => {s with
      contents := s.contents.push <| .inr (x, 1),
    }
    modify fun s => {s with
      indices := s.indices.insert x i
    }
    pure i

instance [h1 : Nonempty α] [h2 : Nonempty β] : Nonempty (α × β) :=
  h1.elim fun x =>
    h2.elim fun y =>
      ⟨(x, y)⟩


example [Inhabited α] [Monad m] [MonadState (State α) m] [BEq α] [Hashable α] (_ : α) : Inhabited (m (Nat × α × Nat)) := inferInstance

-- Lifted from find's where block to make sure the Inhabited instance is found
partial def find.loop [Inhabited α] [Monad m] [MonadState (State α) m] (i : Nat) : m (Nat × α × Nat) := do
    -- Instance needed in Lean 4.12 and onwards, where there's Nonempty but not Inhabited instances
    -- for Sum
    let _ : Inhabited (Nat ⊕ α × Nat) := ⟨.inl default⟩
    match (← get).contents[i]?.get! with
    | .inl j => loop j
    | .inr (v, sz) => return (i, v, sz)

def find [Inhabited α] [Monad m] [MonadState (State α) m] [BEq α] [Hashable α] (x : α) : m (Nat × α × Nat) := do
  find.loop <| ← insert x

def equate [Inhabited α] [Monad m] [MonadState (State α) m] [BEq α] [Hashable α] (x y : α) : m Unit := do
  let mut x' ← find x
  let mut y' ← find y
  if x'.fst == y'.fst then return
  if x'.2.2 < y'.2.2 then
    let tmp := x'
    x' := y'
    y' := tmp
  modify fun s => {s with contents := s.contents.set! y'.fst (.inl x'.fst)}
  modify fun s => {s with contents := s.contents.set! x'.fst (.inr (x'.2.1, x'.2.2 + y'.2.2))}

def testSetup : StateT (State String) Id Unit := do
  for x in [0:10] do discard <| insert (toString x)
  for x in [0:10:2] do equate "0" (toString x)

end UnionFind

def getRefs (info : Server.RefInfo) : List Lsp.RefIdent :=
  let defn := info.definition.map getNames |>.getD []
  let more := info.usages.map getNames
  more.foldl (· ++ ·) defn
where
  getNames (ref : Server.Reference) : List Lsp.RefIdent :=
    ref.ident :: ref.aliases.toList

def build (refs : Server.ModuleRefs) : HashMap Lsp.RefIdent Lsp.RefIdent := Id.run do
  let st := go refs.toList |>.run .init |>.snd
  let mut ids : HashMap _ _ := {}
  for (x, _) in st.indices.toList do
    let ((_, y, _), _) := StateT.run (m := Id) (UnionFind.find x) st
    ids := ids.insert x y
  ids
where
  go : List (Lsp.RefIdent × Server.RefInfo) → StateT (UnionFind.State Lsp.RefIdent) Id Unit
    | [] => pure ()
    | (x, info) :: more => do
      for y in getRefs info do UnionFind.equate x y
      go more

def exprKind [Monad m] [MonadLiftT IO m] [MonadMCtx m] [MonadEnv m]
    (ids : HashMap Lsp.RefIdent Lsp.RefIdent) (ci : ContextInfo) (lctx : LocalContext) (expr : Expr)
    : m (Option Token.Kind) := do
  let runMeta {α} (act : MetaM α) : m α := ci.runMetaM lctx act
  match ← instantiateMVars expr with
  | Expr.fvar id =>
    let seen ←
      if let some y := ids[(← Compat.mkRefIdentFVar id)]? then
        Compat.refIdentCase y
          (onFVar := fun x => do
            let ty ← instantiateMVars (← runMeta <| Meta.inferType expr)
            let tyStr := toString (← runMeta <| Meta.ppExpr ty)
            if let some localDecl := lctx.find? x then
              if localDecl.isAuxDecl then
                let e ← runMeta <| Meta.ppExpr expr
                -- FIXME the mkSimple is a bit of a kludge
                return some (.const (.mkSimple (toString e)) tyStr none)
            return some (.var x tyStr))
          (onConst := fun x => do
            let sig := toString (← runMeta (PrettyPrinter.ppSignature x)).1
            let docs ← findDocString? (← getEnv) x
            return some (.const x sig docs))
      else
        let ty ← instantiateMVars (← runMeta <| Meta.inferType expr)
        let tyStr := toString (← runMeta <| Meta.ppExpr ty)
        return some (.var id tyStr)
  | Expr.const name _ => --TODO universe vars
    let docs ← findDocString? (← getEnv) name
    let sig := toString (← runMeta (PrettyPrinter.ppSignature name)).1
    return some (.const name sig docs)
  | Expr.sort .. => return some .sort
  | Expr.lit (.strVal s) => return some (.str s)
  | _ => return none

def termInfoKind [Monad m] [MonadLiftT IO m] [MonadMCtx m] [MonadEnv m]
     (ids : HashMap Lsp.RefIdent Lsp.RefIdent) (ci : ContextInfo) (termInfo : TermInfo)
    : m (Option Token.Kind) := exprKind ids ci termInfo.lctx termInfo.expr

def fieldInfoKind [Monad m] [MonadMCtx m] [MonadLiftT IO m] [MonadEnv m]
    (ci : ContextInfo) (fieldInfo : FieldInfo)
    : m Token.Kind := do
  let runMeta {α} (act : MetaM α) : m α := ci.runMetaM fieldInfo.lctx act
  let ty ← instantiateMVars (← runMeta <| Meta.inferType fieldInfo.val)
  let tyStr := toString (← runMeta <| Meta.ppExpr ty)
  let docs ← findDocString? (← getEnv) fieldInfo.projName
  return .const fieldInfo.projName tyStr docs

def infoKind [Monad m] [MonadLiftT IO m] [MonadMCtx m] [MonadEnv m]
     (ids : HashMap Lsp.RefIdent Lsp.RefIdent) (ci : ContextInfo) (info : Info)
    : m (Option Token.Kind) := do
  match info with
    | .ofTermInfo termInfo => termInfoKind ids ci termInfo
    | .ofFieldInfo fieldInfo => some <$> fieldInfoKind ci fieldInfo
    | .ofOptionInfo oi =>
      let doc := (← getOptionDecls).find? oi.optionName |>.map (·.descr)
      pure <| some <| .option oi.optionName oi.declName doc
    | .ofCompletionInfo _ => pure none
    | .ofTacticInfo _ => pure none
    | _ =>
      -- dbg_trace (← info.format ci)
      pure none

def identKind [Monad m] [MonadLiftT IO m] [MonadFileMap m] [MonadEnv m] [MonadMCtx m]
    (ids : HashMap Lsp.RefIdent Lsp.RefIdent) (trees : PersistentArray InfoTree) (stx : TSyntax `ident)
    : m Token.Kind := do
  let mut kind : Token.Kind := .unknown
  for t in trees do
    for (ci, info) in infoForSyntax t stx do
      if let some seen ← infoKind ids ci info then
        if seen.priority > kind.priority then kind := seen
      else continue

  pure kind

def infoExists [Monad m] [MonadLiftT IO m] (trees : PersistentArray InfoTree) (stx : Syntax) : m Bool := do
  for t in trees do
    for _ in infoForSyntax t stx do
      return true
  return false


inductive Output where
  | seq (emitted : Array Highlighted)
  | span (info : Array (Highlighted.Span.Kind × String))
  | tactics (info : Array (Highlighted.Goal Highlighted)) (startPos : Nat) (endPos : Nat)

def Output.add (output : List Output) (hl : Highlighted) : List Output :=
  match output with
  | [] => [.seq #[hl]]
  | .seq left :: more => .seq (left.push hl) :: more
  | .span .. :: _ => .seq #[hl] :: output
  | .tactics .. :: _ => .seq #[hl] :: output

def Output.addToken (output : List Output) (token : Token) : List Output :=
  Output.add output (.token token)

def Output.addText (output : List Output) (str : String) : List Output :=
  Output.add output (.text str)

def Output.openSpan (output : List Output) (messages : Array (Highlighted.Span.Kind × String)) : List Output :=
  .span messages :: output

def Output.inTacticState (output : List Output) (info : Array (Highlighted.Goal Highlighted)) : Bool :=
  output.any fun
    | .tactics info' _ _ => info == info'
    | _ => false

def Output.closeSpan (output : List Output) : List Output :=
  let rec go (acc : Highlighted) : List Output → List Output
    | [] => [.seq #[acc]]
    | .span info :: more => Output.add more (.span info acc)
    | .tactics info startPos endPos :: more => Output.add more (.tactics info startPos endPos acc)
    | .seq left :: more => go (.seq (left.push acc)) more
  go .empty output

def Highlighted.fromOutput (output : List Output) : Highlighted :=
  let rec go (acc : Highlighted) : List Output → Highlighted
    | [] => acc
    | .seq left :: more => go (.seq (left.push acc)) more
    | .span info :: more => go (.span info acc) more
    | .tactics info startPos endPos :: more => go (.tactics info startPos endPos acc) more
  go .empty output

structure OpenTactic where
  closesAt : Lean.Position

structure MessageBundle where
  messages : Array Message
  non_empty : messages.size > 0

def MessageBundle.first (msgs : MessageBundle) : Message := msgs.messages[0]'msgs.non_empty

def MessageBundle.pos (msgs : MessageBundle) : Lean.Position := msgs.first.pos

def MessageBundle.endPos (msgs : MessageBundle) : Option Lean.Position := msgs.first.endPos

private def _root_.Lean.Position.before (pos1 pos2 : Lean.Position) : Bool :=
  pos1.line < pos2.line || (pos1.line == pos2.line && pos1.column < pos2.column)

private def _root_.Lean.Position.notAfter (pos1 pos2 : Lean.Position) : Bool :=
  pos1.line < pos2.line || (pos1.line == pos2.line && pos1.column ≤ pos2.column)

def bundleMessages (msgs : Array Message) : Array MessageBundle := Id.run do
  let mut out := #[]
  let mut curr : Option MessageBundle := none
  for m in msgs.qsort cmp do
    match curr with
    | none => curr := some ⟨#[m], Nat.zero_lt_succ 0⟩
    | some b =>
      let first := b.messages[0]'b.non_empty
      if first.pos == m.pos && first.endPos == m.endPos then
        curr := some {b with
          messages := b.messages.push m,
          non_empty := by rw [Array.size_push]; exact lt_succ_of_lt b.non_empty
        }
      else
        out := out.push b
        curr := some ⟨#[m], Nat.zero_lt_succ 0⟩
  if let some b := curr then out := out.push b
  out
where
  lt_succ_of_lt {n k : Nat} : n < k → n < k + 1 := by
    intro lt
    induction lt <;> apply Nat.lt.step
    . constructor
    . assumption

  cmp (m1 m2 : Message) :=
    if m1.pos.before m2.pos then true
    else if m1.pos == m2.pos then
      match m1.endPos, m2.endPos with
      | none, none => true
      | some _, none => false
      | none, some _ => true
      | some e1, some e2 => e2.before e1
    else false

structure HighlightState where
  /-- Messages not yet displayed -/
  messages : Array MessageBundle
  nextMessage : Option (Fin messages.size)
  /-- Output so far -/
  output : List Output
  /-- Messages being displayed -/
  inMessages : List (MessageBundle ⊕ OpenTactic)
deriving Inhabited

def HighlightState.empty : HighlightState where
  messages := #[]
  nextMessage := none
  output := []
  inMessages := []

def HighlightState.ofMessages [Monad m] [MonadFileMap m]
    (stx : Syntax) (messages : Array Message) : m HighlightState := do
  let msgs ← bundleMessages <$> messages.filterM (isRelevant stx)
  pure {
    messages := msgs
    nextMessage := if h : 0 < msgs.size then some ⟨0, h⟩ else none,
    output := [],
    inMessages := [],
  }
where
  isRelevant (stx : Syntax) (msg : Message) : m Bool := do
    let text ← getFileMap
    let (some s, some e) := (stx.getPos?.map text.toPosition , stx.getTailPos?.map text.toPosition)
      | return false
    if let some e' := msg.endPos then
      pure <| !(e'.before s) && !(e.before msg.pos)
    else
      pure <| !(msg.pos.before s) && !(e.before msg.pos)

abbrev HighlightM (α : Type) : Type := StateT HighlightState TermElabM α

private def modify? (f : α → Option α) : (xs : List α) → Option (List α)
  | [] => none
  | x :: xs =>
    if let some x' := f x then
      some (x' :: xs)
    else (x :: ·) <$> modify? f xs

def HighlightState.openTactic (st : HighlightState) (info : Array (Highlighted.Goal Highlighted)) (startPos endPos : Nat) (pos : Position) : HighlightState :=
  if let some out' := modify? update? st.output then
    {st with output := out'}
  else {st with
    output := .tactics info startPos endPos :: st.output,
    inMessages := .inr ⟨pos⟩ :: st.inMessages
  }
where
  update?
    | .tactics info' startPos' endPos' =>
      if startPos == startPos' && endPos == endPos' then
        some <| .tactics (info ++ info') startPos' endPos'
      else none
    | _ => none

def HighlightM.openTactic (info : Array (Highlighted.Goal Highlighted)) (startPos endPos : Nat) (pos : Position) : HighlightM Unit :=
  modify fun st => st.openTactic info startPos endPos pos

instance : Inhabited (HighlightM α) where
  default := fun _ => default

def nextMessage? : HighlightM (Option MessageBundle) := do
  let st ← get
  match st.nextMessage with
  | none => pure none
  | some i => pure (some st.messages[i])

def advanceMessages : HighlightM Unit := do
  modify fun st =>
    if let some ⟨i, _⟩ := st.nextMessage then
      if h : i + 1 < st.messages.size
        then {st with nextMessage := some ⟨i + 1, h⟩}
        else {st with nextMessage := none}
    else st

-- TODO take a closing position as well to avoid opening too early. Right now,
-- we close too conservatively, leading to error spans that are too small. But
-- not doing that leads to huge error spans! This si because an error on just
-- the opening token of a syntax object is opened when visiting that syntax
-- object. It should wait to open it until the syntax we're looking at is fully
-- contained in the error span.
def needsOpening (pos : Lean.Position) (message : MessageBundle) : Bool :=
  message.pos.notAfter pos

def needsClosing (pos : Lean.Position) (message : MessageBundle) : Bool :=
  message.endPos.map pos.notAfter |>.getD true

partial def openUntil (pos : Lean.Position) : HighlightM Unit := do
  if let some msg ← nextMessage? then
    if needsOpening pos msg then
      advanceMessages
      let str ← msg.messages.mapM fun m => do
          let kind : Highlighted.Span.Kind :=
            match m.severity with
            | .error => .error
            | .warning => .warning
            | .information => .info
          let str ← contents m
          pure (kind, str)

      modify fun st => {st with
        output := Output.openSpan st.output str
        inMessages := .inl msg :: st.inMessages
      }
      openUntil pos
where
  contents (message : Message) : IO String := do
    let head := if message.caption != "" then message.caption ++ ":\n" else ""
    pure <| head ++ (← message.data.toString)


partial def closeUntil (pos : Lean.Position) : HighlightM Unit := do
  let more ← modifyGet fun st =>
    match st.inMessages with
    | [] => (false, st)
    | .inl m :: ms =>
      if needsClosing pos m then
        (true, {st with output := Output.closeSpan st.output, inMessages := ms})
      else (false, st)
    | .inr t :: ms =>
      if t.closesAt.before pos || t.closesAt == pos then
        (true, {st with output := Output.closeSpan st.output, inMessages := ms})
      else (false, st)
  if more then closeUntil pos

def emitString (pos endPos : String.Pos) (string : String) : HighlightM Unit := do
  let text ← getFileMap
  openUntil <| text.toPosition pos
  modify fun st => {st with output := Output.addText st.output string}
  closeUntil <| text.toPosition endPos

def emitString' (string : String) : HighlightM Unit :=
  modify fun st => {st with output := Output.addText st.output string}

def emitToken (info : SourceInfo) (token : Token) : HighlightM Unit := do
  let .original leading pos trailing endPos := info
    | throwError "Syntax not original, can't highlight"
  emitString' leading.toString
  let text ← getFileMap
  openUntil <| text.toPosition pos
  modify fun st => {st with output := Output.addToken st.output token}
  closeUntil <| text.toPosition endPos
  emitString' trailing.toString

def emitToken' (token : Token) : HighlightM Unit := do
  modify fun st => {st with output := Output.addToken st.output token}

def _root_.Lean.Elab.Info.isOriginal (i : Info) : Bool :=
  match i.stx.getHeadInfo, i.stx.getTailInfo with
  | .original .., .original .. => true
  | _, _ => false

partial def subsyntaxes (stx : Syntax) : Array Syntax := Id.run do
  match stx with
  | .node _ _ children =>
    let mut stxs := children
    for s in children.map subsyntaxes do
      stxs := stxs ++ s
    stxs
  | _ => #[]

def hasTactics (stx : Syntax) (trees : PersistentArray Lean.Elab.InfoTree) : HighlightM Bool := do
  for t in trees do
    for (_, i) in infoForSyntax t stx do
      if not i.isOriginal then continue
      if let .ofTacticInfo _ := i then
        return true
  return false

partial def childHasTactics (stx : Syntax) (trees : PersistentArray Lean.Elab.InfoTree) : HighlightM Bool := do
  match stx with
  | .node _ _ children =>
    for s in children do
      if ← hasTactics s trees then
        return true
      if ← childHasTactics s trees then
        return true
    pure false
  | _ => pure false


partial def renderTagged [Monad m] [MonadLiftT IO m] [MonadMCtx m] [MonadEnv m]
    (ids : HashMap Lsp.RefIdent Lsp.RefIdent) (outer : Option Token.Kind) (doc : CodeWithInfos)
    : m Highlighted := do
  match doc with
  | .text txt => do
    -- TODO: fix this upstream in Lean so the infoview also benefits - this hack is terrible
    let mut todo := txt
    let mut toks : Array Highlighted := #[]
    let mut current := ""
    while !todo.isEmpty do
      for kw in ["let", "fun", "do", "match", "with", "if", "then", "else", "break", "continue", "for", "in", "mut"] do
        if kw.isPrefixOf todo && tokenEnder (todo.drop kw.length) then
          if !current.isEmpty then
            if let some k := outer then
              toks := toks.push <| .token ⟨k, current⟩
            else
              toks := toks.push <| .text current
            current := ""
          toks := toks.push <| .token ⟨.keyword none none none, kw⟩
          todo := todo.drop kw.length
          break
      let c := todo.get 0
      current := current.push c
      todo := todo.drop 1
      -- Don't highlight keywords that occur inside other tokens
      if c.isAlphanum then
        let tok := todo.takeWhile Char.isAlphanum
        current := current ++ tok
        todo := todo.drop tok.length

    if !current.isEmpty then
      if let some k := outer then
        toks := toks.push <| .token ⟨k, current⟩
      else
        toks := toks.push <| .text current
    pure <| if let #[t] := toks then t else .seq toks
  | .tag t doc' =>
    let ⟨{ctx, info, children := _}⟩ := t.info
    if let .text tok := doc' then
      if let some k ← infoKind ids ctx info then
        pure <| .token ⟨k, tok⟩
      else pure <| .text tok
    else
      let k? ← infoKind ids ctx info
      renderTagged ids k? doc'
  | .append xs => .seq <$> xs.mapM (renderTagged ids outer)
where
  tokenEnder str := str.isEmpty || !(str.get 0 |>.isAlphanum)

partial def _root_.Lean.Widget.TaggedText.oneLine (txt : TaggedText α) : Bool :=
  match txt with
  | .text txt => !(txt.contains '\n')
  | .tag _ doc => doc.oneLine
  | .append docs => docs.all (·.oneLine)

partial def _root_.Lean.Widget.TaggedText.indent (doc : TaggedText α) : TaggedText α :=
  let rec indent'
    | .text txt => .text (txt.replace "\n" "\n  ")
    | .tag t doc' => .tag t (indent' doc')
    | .append docs => .append (docs.map indent')
  .append #[.text "  ", indent' doc]

def highlightGoals
    (ids : HashMap Lsp.RefIdent Lsp.RefIdent)
    (ci : ContextInfo)
    (goals : List MVarId)
    : HighlightM (Array (Highlighted.Goal Highlighted)) := do
  let mut goalView := #[]
  for g in goals do
    let mut hyps := #[]
    let some mvDecl := ci.mctx.findDecl? g
      | continue
    let name := if mvDecl.userName.isAnonymous then none else some mvDecl.userName
    let lctx := mvDecl.lctx |>.sanitizeNames.run' {options := (← getOptions)}

    -- Tell the delaborator to tag functions that are being applied. Otherwise,
    -- functions have no tooltips or binding info in tactics.
    -- cf https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Function.20application.20delaboration/near/265800665
    let ci' := {ci with options := ci.options.set `pp.tagAppFns true}
    let runMeta {α} (act : MetaM α) : HighlightM α := ci'.runMetaM lctx act
    for c in lctx.decls do
      let some decl := c
        | continue
      if decl.isAuxDecl || decl.isImplementationDetail then continue
      match decl with
      | .cdecl _index fvar name type _ _ =>
        let nk ← exprKind ids ci lctx (.fvar fvar)
        let tyStr ← renderTagged ids none (← runMeta (ppExprTagged =<< instantiateMVars type))
        hyps := hyps.push (name, nk.getD .unknown, tyStr)
      | .ldecl _index fvar name type val _ _ =>
        let nk ← exprKind ids ci lctx (.fvar fvar)
        let tyDoc ← runMeta (ppExprTagged =<< instantiateMVars type)
        let valDoc ← runMeta (ppExprTagged =<< instantiateMVars val)
        let tyValStr ← renderTagged ids none <| .append <| #[tyDoc].append <|
          if tyDoc.oneLine && valDoc.oneLine then #[.text " := ", valDoc]
          else #[.text " := \n", valDoc.indent]
        hyps := hyps.push (name, nk.getD .unknown, tyValStr)
    let concl ← renderTagged ids none (← runMeta <| ppExprTagged =<< instantiateMVars mvDecl.type)
    goalView := goalView.push ⟨name, Meta.getGoalPrefix mvDecl, hyps, concl⟩
  pure goalView

partial def findTactics'
    (ids : HashMap Lsp.RefIdent Lsp.RefIdent)
    (trees : PersistentArray Lean.Elab.InfoTree)
    (stx : Syntax)
    (startPos endPos : String.Pos)
    (endPosition : Position)
    (before : Bool := false)
    : HighlightM (Option (Array (Highlighted.Goal Highlighted) × Nat × Nat × Position)) := do
  for t in trees do
    -- The info is reversed here so that the _last_ state computed is shown.
    -- This makes `repeat` do the right thing, rather than either spamming
    -- states or showing the first one.
    for i in infoForSyntax t stx |>.reverse do
      if not i.2.isOriginal then continue
      if let (ci, .ofTacticInfo tacticInfo) := i then
        if !before && !tacticInfo.goalsBefore.isEmpty && tacticInfo.goalsAfter.isEmpty then
          return some (#[], startPos.byteIdx, endPos.byteIdx, endPosition)

        let goals := if before then tacticInfo.goalsBefore else tacticInfo.goalsAfter
        if goals.isEmpty then continue
        let goalView ← highlightGoals ids ci goals

        if !Output.inTacticState (← get).output goalView then
          return some (goalView, startPos.byteIdx, endPos.byteIdx, endPosition)
  return none

partial def findTactics
    (ids : HashMap Lsp.RefIdent Lsp.RefIdent)
    (trees : PersistentArray Lean.Elab.InfoTree)
    (stx : Syntax)
    : HighlightM (Option (Array (Highlighted.Goal Highlighted) × Nat × Nat × Position)) :=
  withTraceNode `SubVerso.Highlighting.Code (fun x => pure m!"findTactics {stx} ==> {match x with | .error _ => "err" | .ok v => v.map (fun _ => "yes") |>.getD "no"}") <| do
  let text ← getFileMap
  let some startPos := stx.getPos?
    | return none
  let some endPos := stx.getTailPos?
    | return none
  let endPosition := text.toPosition endPos

  -- Blacklisted tactics. TODO: make into an extensible table.
  -- `;` is blacklisted  - no need to highlight states identically
  if stx matches .atom _ ";" then return none

  -- Place the initial proof state after the `by` token
  if stx matches .atom _ "by" then
    for t in trees do
      for i in infoIncludingSyntax t stx |>.reverse do
        if not i.2.isOriginal then continue
        if let (_, .ofTacticInfo tacticInfo) := i then
          match tacticInfo.stx with
          | `(Lean.Parser.Term.byTactic| by%$tk $tactics)
          | `(Lean.Parser.Term.byTactic'| by%$tk $tactics) =>
            if tk == stx then
              return (← findTactics' ids trees tactics startPos endPos endPosition (before := true))
          | _ => continue

  -- Special handling for =>: show the _before state_
  if stx matches .atom _ "=>" then
    for t in trees do
      for i in infoIncludingSyntax t stx |>.reverse do
        if not i.2.isOriginal then continue
        if let (_, .ofTacticInfo tacticInfo) := i then
          match tacticInfo.stx with
          | `(Lean.Parser.Tactic.inductionAlt| $_lhs =>%$tk $rhs )
          | `(tactic| next $_* =>%$tk $rhs )
          | `(tactic| case $_ $_* =>%$tk $rhs )
          | `(tactic| case' $_ $_* =>%$tk $rhs ) =>
            if tk == stx then
              return (← findTactics' ids trees rhs startPos endPos endPosition (before := true))
          | _ => continue

  -- Only show tactic output for the most specific source spans possible, with a few exceptions
  if stx.getKind ∉ [``Lean.Parser.Tactic.rwSeq,``Lean.Parser.Tactic.simp] then
    if ← childHasTactics stx trees then return none

  -- Override states - some tactics show many intermediate states, which is overwhelming in rendered
  -- output. Get the right one to show for the whole thing, then adjust its positioning.
  if let `(tactic|rw $[$_c:config]? [$_rs,*]%$brak $[$_l:location]?) := stx then
    if let some (goals, _startPos, _endPos, _endPosition) ← findTactics ids trees brak then
      return some (goals, startPos.byteIdx, endPos.byteIdx, endPosition)

  findTactics' ids trees stx startPos endPos endPosition


partial def highlight'
    (ids : HashMap Lsp.RefIdent Lsp.RefIdent)
    (trees : PersistentArray Lean.Elab.InfoTree)
    (stx : Syntax)
    (tactics : Bool)
    (lookingAt : Option (Name × String.Pos) := none)
    : HighlightM Unit :=
  withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"Highlighting {stx}") do
  let mut tactics := tactics
  if tactics then
    if let some (tacticInfo, startPos, endPos, position) ← findTactics ids trees stx then
      HighlightM.openTactic tacticInfo startPos endPos position
      -- No nested tactics - the tactic search process should only have returned results
      -- on "leaf" nodes anyway
      tactics := false
  match stx with
  | `($e.%$tk$field:ident) =>
      highlight' ids trees e tactics
      if let some ⟨pos, endPos⟩ := tk.getRange? then
        emitToken tk.getHeadInfo <| .mk .unknown <| (← getFileMap).source.extract pos endPos
      else
        emitString' "."
      highlight' ids trees field tactics
  | _ =>
    match stx with
    | .missing => pure () -- TODO emit unhighlighted string
    | .ident _ _ .anonymous _ =>
      -- If the anonymous identifier occurs, it's because it was a fallback for an optional
      -- identifier (e.g. in `have`) and the user didn't write it.
      pure ()
    | stx@(.ident i _ x _) =>
        match x.eraseMacroScopes with
        | .str (.str _ _) _ =>
          match stx.identComponents (nFields? := some 1) with
          | [y, field] =>
            if (← infoExists trees field) then
              highlight' ids trees y tactics
              emitToken' <| fakeToken .unknown "."
              highlight' ids trees field tactics
            else
              emitToken i ⟨← identKind ids trees ⟨stx⟩, x.toString⟩
          | _ => emitToken i ⟨← identKind ids trees ⟨stx⟩, x.toString⟩
        | _ => emitToken i ⟨← identKind ids trees ⟨stx⟩, x.toString⟩
    | stx@(.atom i x) =>
      let docs ← match lookingAt with
        | none => pure none
        | some (n, _) => findDocString? (← getEnv) n
      let name := lookingAt.map (·.1)
      let occ := lookingAt.map fun (n, pos) => s!"{n}-{pos}"
      if let .sort ← identKind ids trees ⟨stx⟩ then
        emitToken i ⟨.sort, x⟩
        return
      else
        emitToken i <| (⟨ ·,  x⟩) <|
        match x.get? 0 with
        | some '#' =>
          match x.get? ((0 : String.Pos) + '#') with
          | some c =>
            if c.isAlpha then .keyword name occ docs
            else .unknown
          | _ => .unknown
        | some c =>
          if c.isAlpha then .keyword name occ docs
          else .unknown
        | _ => .unknown
    | .node _ `str #[.atom i string] =>
      if let some s := Syntax.decodeStrLit string then
        emitToken i ⟨.str s, string⟩
      else
        emitToken i ⟨.unknown, string⟩
    | .node _ ``Lean.Parser.Command.docComment #[.atom i1 opener, .atom i2 body] =>
      if let .original leading pos ws _ := i1 then
        if let .original ws' _ trailing endPos := i2 then
          emitToken (.original leading pos trailing endPos) ⟨.docComment, opener ++ ws.toString ++ ws'.toString ++ body⟩
          return
      emitString' (opener ++ " " ++ body ++ "\n")
    | .node _ ``Lean.Parser.Term.dotIdent #[dot@(.atom i _), name@(.ident i' _ x _)] =>
      match i, i' with
      | .original leading pos _ _, .original _ _ trailing endPos =>
        let info := .original leading pos trailing endPos
        emitToken info ⟨← identKind ids trees ⟨stx⟩, s!".{x.toString}"⟩
      | _, _ =>
        highlight' ids trees dot tactics
        highlight' ids trees name tactics
    | .node _ `choice alts =>
      -- Arbitrarily select one of the alternatives found by the parser. Otherwise, quotations of
      -- let-bindings with antiquotations as the bound variable leads to doubled bound variables,
      -- because the parser emits a choice node in the quotation. And it's never correct to show
      -- both alternatives!
      if h : alts.size > 0 then
        highlight' ids trees alts[0]  tactics
    | stx@(.node _ k children) =>
      let pos := stx.getPos?
      for child in children do
        highlight' ids trees child tactics (lookingAt := pos.map (k, ·))

def highlight (stx : Syntax) (messages : Array Message) (trees : PersistentArray Lean.Elab.InfoTree) : TermElabM Highlighted := do
  let modrefs := Lean.Server.findModuleRefs (← getFileMap) trees.toArray
  let ids := build modrefs
  let st ← HighlightState.ofMessages stx messages
  let ((), {output := output, ..}) ← StateT.run (highlight' ids trees stx true) st
  pure <| .fromOutput output

def highlightProofState (ci : ContextInfo) (goals : List MVarId) (trees : PersistentArray Lean.Elab.InfoTree) : TermElabM (Array (Highlighted.Goal Highlighted)) := do
  let modrefs := Lean.Server.findModuleRefs (← getFileMap) trees.toArray
  let ids := build modrefs
  let (hlGoals, _) ← StateT.run (highlightGoals ids ci goals) .empty
  pure hlGoals
