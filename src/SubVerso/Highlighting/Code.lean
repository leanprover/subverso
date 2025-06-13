/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Widget.InteractiveCode
import Lean.Widget.TaggedText


import SubVerso.Compat
import SubVerso.Highlighting.Highlighted
import SubVerso.Highlighting.Messages

open Lean hiding perhaps (HashMap)
open Elab
open Lean.Widget (TaggedText)
open Lean.Widget
open Lean.PrettyPrinter (InfoPerPos)
open SubVerso.Compat (HashMap)


namespace SubVerso.Highlighting

/--
A table that maps source regions to info.

SubVerso has very different access patterns from the language server, and was needing to re-traverse
the info tree in ways that took too much time while finding proof states. This solution
pre-processes it once, saving the info in an easier-to-query form for this use case.

Other info types may be added as needed for performance in the future.
-/
structure InfoTable where
  tacticInfo : Compat.HashMap String.Range (Array (ContextInfo × TacticInfo)) := {}

instance : Inhabited InfoTable := ⟨⟨{}⟩⟩

/--
Adds info to the table, doing nothing if it's not a type that the table supports.
-/
def InfoTable.add (ctx : ContextInfo) (i : Info) (table : InfoTable) : InfoTable :=
  match i with
  | .ofTacticInfo ti =>
    if let some rng := ti.stx.getRange? (canonicalOnly := true) then
      { table with tacticInfo := table.tacticInfo.insert rng <|
        ((Compat.HashMap.get? table.tacticInfo rng).getD #[]).push (ctx, ti)
      }
    else table
  | _ => table

partial def InfoTable.ofInfoTree (t : InfoTree) (init : InfoTable := {}) : InfoTable := go none t init
where
  go (ctx? : Option ContextInfo) (t : InfoTree) (table : InfoTable) : InfoTable :=
    match ctx?, t with
    | ctx?, .context ctx t => go (ctx.mergeIntoOuter? ctx?) t table
    | some ctx, .node i cs => cs.foldl (init := table.add ctx i) fun tbl' t' => go (some ctx) t' tbl'
    | none, .node .. => panic! "Unexpected contextless node"
    | _, .hole _ => table

def InfoTable.ofInfoTrees (ts : Array InfoTree) (init : InfoTable := {}) : InfoTable :=
  ts.foldl (init := init) (fun tbl t => .ofInfoTree t (init := tbl))

def InfoTable.tacticInfo? (stx : Syntax) (table : InfoTable) : Option (Array (ContextInfo × TacticInfo)) := do
  let rng ← stx.getRange? (canonicalOnly := true)
  Compat.HashMap.get? table.tacticInfo rng |>.map (·.filter (·.2.stx == stx))

structure Context where
  ids : HashMap Lsp.RefIdent Lsp.RefIdent
  definitionsPossible : Bool
  suppressNamespaces : List Name

def Context.noDefinitions (ctxt : Context) : Context := {ctxt with definitionsPossible := false}

partial def Token.Kind.priority : Token.Kind → Nat
  | .var .. => 2
  | .str .. => 3
  | .const .. => 5
  | .anonCtor .. => 6
  | .option .. => 4
  | .sort .. => 4
  | .keyword _ _ _ => 3
  | .levelConst .. | .levelVar .. | .levelOp .. => 4
  | .docComment | .withType .. => 1
  | .unknown => 0

/-- Finds all info nodes whose canonical span matches the given syntax -/
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

/--
Removes the unwanted namespaces in question when they occur as prefixes.
-/
partial def stripNamespaces [Monad m] [MonadReaderOf Context m] : FormatWithInfos → m Std.Format
  | ⟨fmt, infos⟩ => do
    match fmt with
    | .text str =>
      -- only rewrite when it's just the name - this is a heuristic that seems to work in practice
      for i in (← read).suppressNamespaces do
        let ns := i.toString ++ "."
        if ns.isPrefixOf str then
          return .text (str.drop ns.length)
      pure <| .text str -- only rewrite when tagged
    | .tag x fmt' =>
      if let some i := infos.find? x then
        match i, fmt' with
        | .ofTermInfo _, .text str =>
          let mut str := str
          for i in (← read).suppressNamespaces do
            str := str.replace (i.toString ++ ".") ""
          return .text str
        | _, _ => stripNamespaces fmt'
      else stripNamespaces fmt'
    | .group fmt' f => (.group · f) <$> stripNamespaces fmt'
    | .append fmt' fmt'' => .append <$> stripNamespaces fmt' <*> stripNamespaces fmt''
    | .nest n fmt' => .nest n <$> stripNamespaces fmt'
    | .line => pure .line
    | .align b => pure (.align b)
    | .nil => pure .nil


def exprKind [Monad m] [MonadLiftT IO m] [MonadMCtx m] [MonadEnv m] [Alternative m]
    (ci : ContextInfo) (lctx : LocalContext) (stx? : Option Syntax) (expr : Expr)
    (allowUnknownTyped : Bool := false)
    : ReaderT Context m (Option Token.Kind) := do
  let runMeta {α} (act : MetaM α) (env := ci.env) (lctx := lctx) : m α := {ci with env := env}.runMetaM lctx act
  -- Print the signature in an empty local context to avoid local auxiliary definitions from
  -- elaboration, which may otherwise shadow in recursive occurrences, leading to spurious `_root_.`
  -- qualifiers
  let ppSig x (env := ci.env) : ReaderT Context m String := do
    let sig ← runMeta (env := env) (lctx := {}) (PrettyPrinter.ppSignature x)
    return toString (← stripNamespaces sig)

  let rec findKind e := do
    match e with
    | Expr.fvar id =>
      let seen ←
        if let some y := (← read).ids[(← Compat.mkRefIdentFVar id)]? then
          Compat.refIdentCase y
            (onFVar := fun x => do
              let ty ← instantiateMVars (← runMeta <| Meta.inferType expr)
              let tyStr := toString (← runMeta <| Meta.ppExpr ty)
              if let some localDecl := lctx.find? x then
                if localDecl.isAuxDecl then
                  let e ← runMeta <| Meta.ppExpr expr
                  -- FIXME the mkSimple is a bit of a kludge
                  return some <| .const (.mkSimple (toString e)) tyStr none false
              return some <| .var x tyStr)
            (onConst := fun x => do
              -- This is a bit of a hack. The environment in the ContextInfo may not have some
              -- helper constants from where blocks yet, so we retry in the final environment if the
              -- first one fails.
              let sig ← ppSig x <|> ppSig (env := (← getEnv)) x
              let docs ← findDocString? (← getEnv) x
              return some <| .const x sig docs false)
        else
          let ty ← instantiateMVars (← runMeta <| Meta.inferType expr)
          let tyStr := toString (← runMeta <| Meta.ppExpr ty)
          return some <| .var id tyStr
    | Expr.const name _ =>
      let docs ← findDocString? (← getEnv) name
      let sig ← ppSig name
      return some <| .const name sig docs false
    | Expr.sort _ =>
      if let some stx := stx? then
        let k := stx.getKind
        let docs? ← findDocString? (← getEnv) k
        return some (.sort docs?)
      else return some (.sort none)
    | Expr.lit (.strVal s) => return some <| .str s
    | Expr.mdata _ e =>
      findKind e
    | other =>
      if allowUnknownTyped then
        runMeta do
          try
            let t ← Meta.inferType other >>= instantiateMVars >>= Meta.ppExpr
            return some <| .withType <| toString t
          catch _ =>
            return none
      else
        return none

  findKind (← instantiateMVars expr)

/-- Checks whether an occurrence of a name is in fact the definition of the name -/
def isDefinition [Monad m] [MonadEnv m] [MonadLiftT IO m] [MonadFileMap m] (name : Name) (stx : Syntax) : m Bool := do
  -- This gets called a lot, so it's important to bail early if it's not likely to be a global
  -- definition. Right now, all global definitions in Lean use `declId` to enable explicit universe
  -- polymorphism, except for constructors. This does mean that `example` and `instance` won't work
  -- yet, but they're a more marginal use case - there's no name to hyperlink to them in rendered
  -- HTML.
  if !((← getEnv).isConstructor name || (← getEnv).isProjectionFn name || stx.getKind == ``Parser.Command.declId) then return false
  if let .none := stx.getHeadInfo then return false
  let ranges :=
    if let some r := (← findDeclarationRangesCore? name) then
      some r
    else (← builtinDeclRanges.get (m := IO)).find? name
  if let some declRanges := ranges then
    let some range ← Compat.getDeclarationRange? stx | return false
    return range == declRanges.range || range == declRanges.selectionRange
  return false

def termInfoKind [Monad m] [MonadLiftT IO m] [MonadMCtx m] [MonadEnv m] [MonadFileMap m] [Alternative m]
    (ci : ContextInfo) (termInfo : TermInfo) (allowUnknownTyped : Bool := false)
    : ReaderT Context m (Option Token.Kind) := do
  let k ← exprKind ci termInfo.lctx termInfo.stx termInfo.expr (allowUnknownTyped := allowUnknownTyped)
  if (← read).definitionsPossible then
    if let some (.const name sig docs _isDef) := k then
      (some ∘ .const name sig docs) <$> (fun _ctxt => isDefinition name termInfo.stx)
    else return k
  else return k

def fieldInfoKind [Monad m] [MonadMCtx m] [MonadLiftT IO m] [MonadEnv m]
    (ci : ContextInfo) (fieldInfo : FieldInfo)
    : m Token.Kind := do
  let runMeta {α} (act : MetaM α) : m α := ci.runMetaM fieldInfo.lctx act
  let ty ← instantiateMVars (← runMeta <| Meta.inferType fieldInfo.val)
  let tyStr := toString (← runMeta <| Meta.ppExpr ty)
  let docs ← findDocString? (← getEnv) fieldInfo.projName
  return .const fieldInfo.projName tyStr docs false

def infoKind [Monad m] [MonadLiftT IO m] [MonadMCtx m] [MonadEnv m] [MonadFileMap m] [Alternative m]
    (ci : ContextInfo) (info : Info) (allowUnknownTyped : Bool := false)
    : ReaderT Context m (Option Token.Kind) := do
  match info with
    | .ofTermInfo termInfo => termInfoKind ci termInfo (allowUnknownTyped := allowUnknownTyped)
    | .ofFieldInfo fieldInfo => some <$> fieldInfoKind ci fieldInfo
    | .ofOptionInfo oi =>
      let doc := (← getOptionDecls).find? oi.optionName |>.map (·.descr)
      pure <| some <| .option oi.optionName oi.declName doc
    | .ofCompletionInfo _ => pure none
    | .ofTacticInfo _ => pure none
    | .ofCommandInfo _ => pure none
    | .ofMacroExpansionInfo _ => pure none
    | .ofUserWidgetInfo _ => pure none
    | _ =>
      pure none

def identKind [Monad m] [MonadLiftT IO m] [MonadFileMap m] [MonadEnv m] [MonadMCtx m] [Alternative m]
    (trees : Array InfoTree) (stx : TSyntax `ident)
    (allowUnknownTyped : Bool := false)
    : ReaderT Context m Token.Kind := do
  let mut kind : Token.Kind := .unknown
  for t in trees do
    for (ci, info) in infoForSyntax t stx do
      if let some seen ← infoKind ci info (allowUnknownTyped := allowUnknownTyped) then
        if seen.priority > kind.priority then kind := seen
      else continue
  pure kind

def anonCtorKind [Monad m] [MonadLiftT IO m] [MonadFileMap m] [MonadEnv m] [MonadMCtx m] [Alternative m]
    (trees : Array InfoTree) (stx : Syntax)
    : ReaderT Context m (Option Token.Kind) := do
  let mut kind : Token.Kind := .unknown
  for t in trees do
    for (ci, info) in infoForSyntax t stx do
      if let some seen ← infoKind ci info then
        if seen.priority > kind.priority then kind := seen
      else continue
  return match kind with
  | .const n sig doc? _ => some <| .anonCtor n sig doc?
  | .anonCtor .. => some kind
  | _ => none

def infoExists [Monad m] [MonadLiftT IO m] (trees : Array InfoTree) (stx : Syntax) : m Bool := do
  for t in trees do
    for _ in infoForSyntax t stx do
      return true
  return false


inductive Output where
  | seq (emitted : Array Highlighted)
  | span (info : Array (Highlighted.Span.Kind × String)) (startPos : String.Pos) (endPos : Option String.Pos)
  | tactics (info : Array (Highlighted.Goal Highlighted)) (startPos : String.Pos) (endPos : String.Pos)
deriving Repr

-- Tactic info regions are detected based on the entire syntax of a term or tactic, but the leading
-- whitespace of the first token has not yet been emitted when they are found. The tactic region
-- should start at the first token of its syntax, so we need to detect the leading whitespace
-- situation.
def Output.addText (output : List Output) (text : String) : List Output :=
  if text.isEmpty then output
  else
    match output with
    | [] => [.seq #[.text text]]
    | .seq left :: more =>
      if left.all (·.isEmpty) then
        Output.addText more text
      else
        .seq (left.push (.text text)) :: more
    -- Spans are opened at the start of a token proper, so no need for special handling
    | .span .. :: _ =>
      .seq #[.text text] :: output
    -- Tactics are opened based on syntax, rather than tokens, so here we need to avoid including
    -- their leading whitespace
    | t@(.tactics ..) :: more =>
      t :: Output.addText more text

def Output.add (output : List Output) (hl : Highlighted) : List Output :=
  if let .text txt := hl then
    Output.addText output txt
  else
    match output with
    | [] => [.seq #[hl]]
    | .seq left :: more => .seq (left.push hl) :: more
    | .span .. :: _ => .seq #[hl] :: output
    | .tactics .. :: _ => .seq #[hl] :: output

def Output.addToken (output : List Output) (token : Token) : List Output :=
  Output.add output (.token token)

def Output.openSpan (output : List Output) (messages : Array (Highlighted.Span.Kind × String)) (startPos : String.Pos) (endPos : Option String.Pos) : List Output :=
  match output with
  | t@(.tactics _ start stop) :: output' =>
    if start == startPos && (endPos.map (fun e => (stop ≤ e : Bool)) |>.getD false) then
      t :: Output.openSpan output' messages startPos endPos
    else
      .span messages startPos endPos :: output
  | h@(.seq hl) :: output' =>
    if hl.all (·.isEmpty) then
      h :: Output.openSpan output' messages startPos endPos
    else
      .span messages startPos endPos :: output
  | _ => .span messages startPos endPos :: output

def Output.inTacticState (output : List Output) (info : Array (Highlighted.Goal Highlighted)) : Bool :=
  output.any fun
    | .tactics info' _ _ => info == info'
    | _ => false

def Output.closeSpan (output : List Output) : List Output :=
  let rec go (acc : Highlighted) : List Output → List Output
    | [] => [.seq #[acc]]
    | .span info _ _ :: more =>
      Output.add more (.span info acc)
    | .tactics info startPos endPos :: more =>
      Output.add more (.tactics info startPos.byteIdx endPos.byteIdx acc)
    | .seq left :: more =>
      go (.seq (left.push acc)) more
  go .empty output

def Highlighted.fromOutput (output : List Output) : Highlighted :=
  let rec go (acc : Highlighted) : List Output → Highlighted
    | [] => acc
    | .seq left :: more => go (.seq (left.push acc)) more
    | .span info _ _ :: more => go (.span info acc) more
    | .tactics info startPos endPos :: more => go (.tactics info startPos.byteIdx endPos.byteIdx acc) more
  go .empty output

structure OpenTactic where
  openedAt : String.Pos
  closesAt : String.Pos

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
  inMessages : List MessageBundle
  /-- Currently-open tactic info -/
  inTactic : Option OpenTactic -- No nested tactic states!
  /-- Memoized results of searching for tactic info (by canonical range) -/
  hasTacticCache : Compat.HashMap String.Range (Array (Syntax × Bool)) := {}
  /-- Memoized results of searching for tactic info in children (by canonical range) -/
  childHasTacticCache : Compat.HashMap String.Range (Array (Syntax × Bool)) := {}

instance : Inhabited HighlightState := ⟨default, default, default, default, default, {}, {}⟩

def HighlightState.empty : HighlightState where
  messages := #[]
  nextMessage := none
  output := []
  inMessages := []
  inTactic := none

def HighlightState.ofMessages [Monad m] [MonadFileMap m]
    (stx : Syntax) (messages : Array Message) : m HighlightState := do
  let msgs ← bundleMessages <$> messages.filterM (isRelevant stx)
  pure {
    messages := msgs
    nextMessage := if h : 0 < msgs.size then some ⟨0, h⟩ else none,
    output := [],
    inMessages := [],
    inTactic := none
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

abbrev HighlightM (α : Type) : Type := ReaderT Context (ReaderT InfoTable (StateRefT HighlightState TermElabM)) α

private def modify? (f : α → Option α) : (xs : List α) → Option (List α)
  | [] => none
  | x :: xs =>
    if let some x' := f x then
      some (x' :: xs)
    else (x :: ·) <$> modify? f xs

def HighlightState.openTactic (st : HighlightState) (info : Array (Highlighted.Goal Highlighted)) (startPos endPos : String.Pos) (_pos : Position) : HighlightState :=
  if let some out' := modify? update? st.output then
    {st with output := out'}
  else { st with
    output := .tactics info startPos endPos :: st.output,
    inTactic := some ⟨startPos, endPos⟩
  }
where
  update?
    | .tactics info' startPos' endPos' =>
      if startPos == startPos' && endPos == endPos' then
        some <| .tactics (info ++ info') startPos' endPos'
      else none
    | _ => none

def HighlightM.openTactic (info : Array (Highlighted.Goal Highlighted)) (startPos endPos : String.Pos) (pos : Position) : HighlightM Unit :=
  modify fun st => st.openTactic info startPos endPos pos

instance : Inhabited (HighlightM α) where
  default := fun _ _ _ => default

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

def needsOpening (pos : Lean.Position) (message : MessageBundle) : Bool :=
  message.pos.notAfter pos

def needsClosing (pos : Lean.Position) (message : MessageBundle) : Bool :=
  message.endPos.map (·.notAfter pos) |>.getD true


partial def openUntil (pos : Lean.Position) : HighlightM Unit := do
  let text ← getFileMap
  if let some msg ← nextMessage? then
    if needsOpening pos msg then
      advanceMessages
      let str ← msg.messages.mapM fun m => do
          let kind : Highlighted.Span.Kind :=
            match SubVerso.Highlighting.Messages.severity m with
            | .error => .error
            | .warning => .warning
            | .information => .info
          let str ← contents m
          pure (kind, str)

      modify fun st =>
    {st with
        output := Output.openSpan st.output str (text.lspPosToUtf8Pos (text.leanPosToLspPos msg.pos)) (msg.endPos.map (text.lspPosToUtf8Pos <| text.leanPosToLspPos ·))
        inMessages := msg :: st.inMessages
      }
      openUntil pos
where
  contents (message : Message) : IO String := do
    let head := if message.caption != "" then message.caption ++ ":\n" else ""
    pure <| head ++ (← message.data.toString)


partial def closeUntil (pos : String.Pos) : HighlightM Unit := do
  let text ← getFileMap
  let more ← modifyGet fun st =>
    match st.inMessages, st.inTactic with
    | [], none => (false, st)
    | [], some t =>
      if t.closesAt ≤ pos || t.closesAt == pos then
        (true, {st with output := Output.closeSpan st.output, inTactic := none})
      else (false, st)
    | m :: ms, none =>
      if needsClosing (text.toPosition pos) m then
        (true, {st with output := Output.closeSpan st.output, inMessages := ms})
      else (false, st)
    | m :: ms, some t =>
      if let some e := m.endPos then
        if text.toPosition t.closesAt |>.notAfter e then
          -- Close the tactics first
          if t.closesAt ≤ pos || t.closesAt == pos then
            (true, {st with output := Output.closeSpan st.output, inTactic := none})
          else (false, st)
        else
          -- Close the message first
          if needsClosing (text.toPosition pos) m then
            (true, {st with output := Output.closeSpan st.output, inMessages := ms})
          else (false, st)
      else (true, {st with output := Output.closeSpan st.output, inMessages := ms})

  if more then closeUntil pos

def emitString (pos endPos : String.Pos) (string : String) : HighlightM Unit := do
  let text ← getFileMap
  openUntil <| text.toPosition pos
  modify fun st => {st with output := Output.addText st.output string}
  closeUntil endPos

def emitString' (string : String) : HighlightM Unit :=
  modify fun st => {st with output := Output.addText st.output string}

def emitToken (blame : Syntax) (info : SourceInfo) (token : Token) : HighlightM Unit := do
  let text ← getFileMap

  let .original leading pos trailing endPos := info
    | match info with
      | .synthetic b e =>
        let str := text.source.extract b e
        throwError "Syntax {blame} not original, can't highlight: '{str}'"
      | _ => throwError "Syntax {blame} not original, can't highlight: {repr info}"

  emitString' leading.toString
  openUntil <| text.toPosition pos
  modify fun st => {st with output := Output.addToken st.output token}
  closeUntil endPos
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

def hasTactics (stx : Syntax) : HighlightM Bool := do
  let rng? := stx.getRange?
  if let some rng := rng? then
    if let some m := Compat.HashMap.get? (← get).hasTacticCache rng then
      for (stx', res) in m do
        if stx' == stx then return res

  if let some info := (← readThe InfoTable).tacticInfo? stx then
    for (_, ti) in info do
      if ti.stx == stx then
        if let some rng := rng? then
          modify fun st =>
            let v := Compat.HashMap.get? st.hasTacticCache rng |>.getD #[] |>.push (stx, true)
            {st with hasTacticCache := st.hasTacticCache.insert rng v}
        return true

  if let some rng := rng? then
    modify fun st =>
      let v := Compat.HashMap.get? st.hasTacticCache rng |>.getD #[] |>.push (stx, false)
      {st with hasTacticCache := st.hasTacticCache.insert rng v}
  return false

partial def childHasTactics (stx : Syntax) : HighlightM Bool := do
  let rng? := stx.getRange?
  if let some rng := rng? then
    if let some m := Compat.HashMap.get? (← get).childHasTacticCache rng then
      for (stx', res) in m do
        if stx' == stx then return res

  let mut res := false
  if let .node _ _ children := stx then
    for s in children do
      if ← hasTactics s then
        res := true
        break
      if ← childHasTactics s then
        res := true
        break

  if let some rng := rng? then
    modify fun st =>
      let v := Compat.HashMap.get? st.childHasTacticCache rng |>.getD #[] |>.push (stx, res)
      {st with childHasTacticCache := st.childHasTacticCache.insert rng v}

  return res


partial def renderTagged [Monad m] [MonadLiftT IO m] [MonadMCtx m] [MonadEnv m] [MonadFileMap m] [Alternative m]
    (outer : Option Token.Kind) (doc : CodeWithInfos)
    : ReaderT Context m Highlighted := do
  match doc with
  | .text txt => do
    -- TODO: fix this upstream in Lean so the infoview also benefits - this hack is terrible
    let mut todo := txt
    let mut toks : Highlighted := .empty
    while !todo.isEmpty do
      let ws := todo.takeWhile (·.isWhitespace)
      unless ws.isEmpty do
        toks := toks ++ .text ws
        todo := todo.drop ws.length

      let mut foundKw := false
      for kw in ["let", "fun", "do", "match", "with", "if", "then", "else", "break", "continue", "for", "in", "mut"] do
        if kw.isPrefixOf todo && tokenEnder (todo.drop kw.length) then
          foundKw := true
          toks := toks ++ .token ⟨.keyword none none none, kw⟩
          todo := todo.drop kw.length
          break
      if foundKw then continue -- for whitespace or subsequent keywords

      -- It's not enough to just push a text node when the token kind isn't set, because that breaks
      -- the code that matches Highlighted against strings for extraction. Instead, we need to split
      -- into tokens vs whitespace here. This assumes there's no comments, because it's used for
      -- pretty printer output.
      let tok := todo.takeWhile (!·.isWhitespace)
      unless tok.isEmpty do
        toks := toks ++ .token ⟨outer.getD .unknown, tok⟩
        todo := todo.drop tok.length

    pure toks
  | .tag t doc' =>
    let {ctx, info, children := _} := t.info.val
    if let .text tok := doc' then
      let wsPre := tok.takeWhile (·.isWhitespace)
      let wsPost := tok.takeRightWhile (·.isWhitespace)
      let k := (← infoKind ctx info).getD .unknown
      pure <| .seq #[.text wsPre, .token ⟨k, tok.trim⟩, .text wsPost]
    else
      let k? ← infoKind ctx info
      renderTagged k? doc'
  | .append xs => xs.mapM (renderTagged outer) <&> (·.foldl (init := .empty) (· ++ ·))
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
    (ci : ContextInfo)
    (goals : List MVarId)
    : HighlightM (Array (Highlighted.Goal Highlighted)) := withReader (·.noDefinitions) do
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
        let nk ← exprKind ci lctx none (.fvar fvar)
        let tyStr ← renderTagged none (← runMeta (ppExprTagged =<< instantiateMVars type))
        hyps := hyps.push (name, nk.getD .unknown, tyStr)
      | .ldecl _index fvar name type val _ _ =>
        let nk ← exprKind ci lctx none (.fvar fvar)
        let tyDoc ← runMeta (ppExprTagged =<< instantiateMVars type)
        let valDoc ← runMeta (ppExprTagged =<< instantiateMVars val)
        let tyValStr ← renderTagged none <| .append <| #[tyDoc].append <|
          if tyDoc.oneLine && valDoc.oneLine then #[.text " := ", valDoc]
          else #[.text " := \n", valDoc.indent]
        hyps := hyps.push (name, nk.getD .unknown, tyValStr)
    let concl ← renderTagged none (← runMeta <| ppExprTagged =<< instantiateMVars mvDecl.type)
    goalView := goalView.push ⟨name, Meta.getGoalPrefix mvDecl, hyps, concl⟩
  pure goalView

def tacticInfoGoals
    (ci : ContextInfo) (tacticInfo : TacticInfo)
    (startPos endPos : String.Pos)
    (endPosition : Position)
    (before : Bool := false) :
    HighlightM (Array (Highlighted.Goal Highlighted) × String.Pos × String.Pos × Position) := do
  let goals := if before then tacticInfo.goalsBefore else tacticInfo.goalsAfter
  let ci := {ci with mctx := if before then tacticInfo.mctxBefore else tacticInfo.mctxAfter}
  let goalView ← highlightGoals ci goals

  return (goalView, startPos, endPos, endPosition)

/--
Finds the tactic info for `stx`, which should be in the indicated span.

If found, returns the goals, the byte indices of the span, and the provided end position.
-/
partial def findTactics'
    (stx : Syntax)
    (startPos endPos : String.Pos)
    (endPosition : Position)
    (before : Bool := false)
    : HighlightM (Option (Array (Highlighted.Goal Highlighted) × String.Pos × String.Pos × Position)) := do

  if let some res := (← readThe InfoTable).tacticInfo? stx then
    for (ci, tacticInfo) in res.reverse do
      if !before && !tacticInfo.goalsBefore.isEmpty && tacticInfo.goalsAfter.isEmpty then
        return some (#[], startPos, endPos, endPosition)

      let goals := if before then tacticInfo.goalsBefore else tacticInfo.goalsAfter
      let ci := {ci with mctx := if before then tacticInfo.mctxBefore else tacticInfo.mctxAfter}
      if goals.isEmpty then continue
      let goalView ← highlightGoals ci goals

      if !Output.inTacticState (← get).output goalView then
        return some (goalView, startPos, endPos, endPosition)

  return none

partial def findTactics
    (trees : Array Lean.Elab.InfoTree) -- TODO: use the table instead of these
    (stx : Syntax)
    : HighlightM (Option (Array (Highlighted.Goal Highlighted) × String.Pos × String.Pos × Position)) :=
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
              let ts ← findTactics' tactics startPos endPos endPosition (before := true)
              return ts
          | _ => continue

  -- Special handling for =>: show the _before state_
  if stx matches .atom _ "=>" then
    for t in trees do
      for i in infoIncludingSyntax t stx |>.reverse do
        if not i.2.isOriginal then continue
        if let (ci, .ofTacticInfo tacticInfo) := i then
          if tacticInfo.stx.getKind == nullKind then
            if let some tacStx := tacticInfo.stx.getArgs.back? then
              if tacStx == stx then
                return some (← tacticInfoGoals ci tacticInfo startPos endPos endPosition (before := true))

          match tacticInfo.stx with
          | `(Lean.Parser.Tactic.inductionAlt| $_lhs =>%$tk $rhs )
          | `(tactic| next $_* =>%$tk $rhs )
          | `(tactic| conv =>%$tk $rhs )
          | `(tactic| conv at $_ =>%$tk $rhs )
          | `(tactic| conv in $_:term =>%$tk $rhs )
          | `(tactic| case $_ $_* =>%$tk $rhs )
          | `(tactic| case' $_ $_* =>%$tk $rhs ) =>
            if tk == stx then
              return (← findTactics' rhs startPos endPos endPosition (before := true))
          | _ => continue

  -- Only show tactic output for the most specific source spans possible, with a few exceptions
  if stx.getKind ∉ [``Lean.Parser.Tactic.rwSeq,``Lean.Parser.Tactic.simp] then
    if ← childHasTactics stx then return none

  -- Override states - some tactics show many intermediate states, which is overwhelming in rendered
  -- output. Get the right one to show for the whole thing, then adjust its positioning.
  if let some brak := Compat.rwTacticRightBracket? stx then
    if let some (goals, _startPos, _endPos, _endPosition) ← findTactics trees brak then
      return some (goals, startPos, endPos, endPosition)

  findTactics' stx startPos endPos endPosition

partial def highlightLevel (u : TSyntax `level) : HighlightM Unit := do
  match u with
  | `(level|$n:num) =>
    emitToken u u.raw.getHeadInfo ⟨.levelConst n.getNat, toString n.getNat⟩
  | `(level|$x:ident) =>
    emitToken u u.raw.getHeadInfo ⟨.levelVar x.getId, toString x.getId⟩
  | `(level|_) =>
    emitToken u u.raw.getHeadInfo ⟨.levelVar .anonymous, toString "_"⟩
  | `(level|(%$s $l:level )%$e) =>
    emitToken u s.getHeadInfo ⟨.unknown, "("⟩
    highlightLevel l
    emitToken e s.getHeadInfo ⟨.unknown, ")"⟩
  | `(level|max%$tk $ls*) =>
    emitToken u tk.getHeadInfo ⟨.levelOp "max", "max"⟩
    for l in ls do
      highlightLevel l
  | `(level|imax%$tk $ls*) =>
    emitToken u tk.getHeadInfo ⟨.levelOp "imax", "imax"⟩
    for l in ls do
      highlightLevel l
  | `(level|$l1 +%$tk $n) =>
    highlightLevel l1
    emitToken u tk.getHeadInfo ⟨.levelOp "+", "+"⟩
    emitToken u n.raw.getHeadInfo ⟨.levelConst n.getNat, toString n.getNat⟩
  | _ => panic! s!"Unknown level syntax {u}"

def highlightUniverse (blame : Syntax) (tk : Syntax) (u : TSyntax `level) : HighlightM Unit := do
  let docs? ← findDocString? (← getEnv) blame.getKind
  emitToken blame tk.getHeadInfo ⟨.sort docs?, tk.getAtomVal⟩ -- TODO sort docs
  highlightLevel u

partial def highlight'
    (trees : Array Lean.Elab.InfoTree)
    (stx : Syntax)
    (tactics : Bool)
    (lookingAt : Option (Name × String.Pos) := none)
    : HighlightM Unit :=
  withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"Highlighting {stx}") do
  let mut tactics := tactics
  if tactics then
    if let some (tacticInfo, startPos, endPos, position) ← findTactics trees stx then
      HighlightM.openTactic tacticInfo startPos endPos position
      -- No nested tactics - the tactic search process should only have returned results
      -- on "leaf" nodes anyway
      tactics := false
  match stx with
  | `($e.%$tk$field:ident) =>
      withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"Highlighting projection {e} {tk} {field}") do
      highlight' trees e tactics
      if let some ⟨pos, endPos⟩ := tk.getRange? then
        emitToken stx tk.getHeadInfo <| .mk .unknown <| (← getFileMap).source.extract pos endPos
      else
        emitString' "."
      highlight' trees field tactics
  | `(term|Type%$s $u) | `(term|Sort%$s $u) => do -- Prop and Type are handled by the atom rules below
    highlightUniverse stx s u
  | _ =>
    match stx with
    | .missing => pure () -- TODO emit unhighlighted string
    | .ident _ _ .anonymous _ =>
      -- If the anonymous identifier occurs, it's because it was a fallback for an optional
      -- identifier (e.g. in `have`) and the user didn't write it.
      pure ()
    | stx@(.ident i _ x _) =>
        withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"Identifier {x}") do
        match x.eraseMacroScopes with
        | .str (.str _ _) _ =>
          match stx.identComponents (nFields? := some 1) with
          | [y, field] =>
            withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"Perhaps a field? {y} {field}") do
            if (← infoExists trees field) then
              withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"Yes, a field!") do
              highlight' trees y tactics
              emitToken' <| fakeToken .unknown "."
              highlight' trees field tactics
            else
              withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"Not a field.") do
              let k ← identKind trees ⟨stx⟩
              withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"Identifier token for {stx} is {repr k}") do
              emitToken stx i ⟨k, x.toString⟩
          | _ =>
            let k ← identKind trees ⟨stx⟩
            withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"Identifier token for {stx} is {repr k}") do
            emitToken stx i ⟨k, x.toString⟩
        | _ =>
          let k ← identKind trees ⟨stx⟩
          withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"Identifier token for {stx} is {repr k}") do
          emitToken stx i ⟨k, x.toString⟩
    | stx@(.atom i x) =>
      withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"Keyword while looking at {lookingAt}") do
      let docs ← match lookingAt with
        | none => pure none
        | some (n, _) => findDocString? (← getEnv) n
      let name := lookingAt.map (·.1)
      let occ := lookingAt.map fun (n, pos) => s!"{n}-{pos}"
      if let .sort docs? ← identKind trees ⟨stx⟩ then
        withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"Sort") do
          emitToken stx i ⟨.sort docs?, x⟩
        return
      else
        emitToken stx i <| (⟨ ·,  x⟩) <|
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
      withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"String") do
      if let some s := Syntax.decodeStrLit string then
        emitToken stx i ⟨.str s, string⟩
      else
        emitToken stx i ⟨.unknown, string⟩
    | .node _ `num #[.atom i n] =>
      withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"Numeral") do
        let k ← identKind trees ⟨stx⟩ (allowUnknownTyped := true)
        emitToken stx i ⟨k, n⟩
    | .node _ ``Lean.Parser.Command.docComment #[.atom i1 opener, .atom i2 body] =>
      withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"Doc comment") do
      if let .original leading pos ws _ := i1 then
        if let .original ws' _ trailing endPos := i2 then
          emitToken stx (.original leading pos trailing endPos) ⟨.docComment, opener ++ ws.toString ++ ws'.toString ++ body⟩
          return
      emitString' (opener ++ " " ++ body ++ "\n")
    | .node _ ``Lean.Parser.Term.dotIdent #[dot@(.atom i _), name@(.ident i' _ x _)] =>
      withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"Dotted identifier") do
      match i, i' with
      | .original leading pos _ _, .original _ _ trailing endPos =>
        let info := .original leading pos trailing endPos
        emitToken stx info ⟨← identKind trees ⟨stx⟩, s!".{x.toString}"⟩
      | _, _ =>
        highlight' trees dot tactics
        highlight' trees name tactics
    | .node _ k@``Lean.Parser.Term.anonymousCtor #[opener@(.atom oi l), children@(.node _ _ contents), closer@(.atom ci r)] =>
      if let some tk ← anonCtorKind trees stx then
        emitToken stx oi ⟨tk, l⟩
        for child in contents do
          match child with
          | .atom commaInfo "," =>
            emitToken stx commaInfo ⟨tk, ","⟩
          | _ =>
            highlight' trees child tactics
        emitToken stx ci ⟨tk, r⟩
      else
        let pos := stx.getPos?
        highlight' trees opener tactics (lookingAt := pos.map (k, ·))
        highlight' trees children tactics (lookingAt := pos.map (k, ·))
        highlight' trees closer tactics (lookingAt := pos.map (k, ·))
    | .node _ `choice alts =>
      withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"Choice node with {alts.size} alternatives") do
      -- Arbitrarily select one of the alternatives found by the parser. Otherwise, quotations of
      -- let-bindings with antiquotations as the bound variable leads to doubled bound variables,
      -- because the parser emits a choice node in the quotation. And it's never correct to show
      -- both alternatives!
      if h : alts.size > 0 then
        highlight' trees alts[0]  tactics
    | stx@(.node _ k children) =>
      withTraceNode `SubVerso.Highlighting.Code (fun _ => pure m!"Other node, kind {k}, with {children.size} children") do
      let pos := stx.getPos?
      for child in children do
        highlight' trees child tactics (lookingAt := pos.map (k, ·))

def highlight (stx : Syntax) (messages : Array Message)
    (trees : PersistentArray Lean.Elab.InfoTree)
    (suppressNamespaces : List Name := []) : TermElabM Highlighted := do
  let trees := trees.toArray
  let modrefs := Lean.Server.findModuleRefs (← getFileMap) trees
  let ids := build modrefs

  let st ← HighlightState.ofMessages stx messages
  let infoTable : InfoTable := .ofInfoTrees trees

  let ((), {output := output, ..}) ← highlight' trees stx true |>.run ⟨ids, true, suppressNamespaces⟩ |>.run infoTable |>.run st
  pure <| .fromOutput output

/--
Highlights a sequence of syntaxes, each with its own info tree. Typically used for highlighting a
module, where each command has its own corresponding tree.

The work of constructing the alias table is performed once, with all the trees together.
-/
def highlightMany (stxs : Array Syntax) (messages : Array Message)
    (trees : Array (Option Lean.Elab.InfoTree))
    (suppressNamespaces : List Name := []) : TermElabM (Array Highlighted) := do
  let trees' := trees.filterMap id
  let infoTable : InfoTable := .ofInfoTrees trees'
  let modrefs := Lean.Server.findModuleRefs (← getFileMap) trees'
  let ids := build modrefs
  let st ← HighlightState.ofMessages (mkNullNode stxs) messages

  if trees.size ≠ stxs.size then throwError "Mismatch: got {trees.size} info trees and {stxs.size} syntaxes"
  let (hls, _) ← (trees.zip stxs).mapM (fun (x, y) => go x y) |>.run ⟨ids, true, suppressNamespaces⟩ |>.run infoTable |>.run st
  pure hls
where
  go t stx := do
    let _ ← highlight' (Option.map (#[·]) t |>.getD #[]) stx true
    modifyGet fun (st : HighlightState) => (Highlighted.fromOutput st.output, {st with output := []})


def highlightProofState (ci : ContextInfo) (goals : List MVarId)
    (trees : PersistentArray Lean.Elab.InfoTree)
    (suppressNamespaces : List Name := []) : TermElabM (Array (Highlighted.Goal Highlighted)) := do
  let trees := trees.toArray
  let modrefs := Lean.Server.findModuleRefs (← getFileMap) trees
  let ids := build modrefs
  let infoTable : InfoTable := .ofInfoTrees trees
  let (hlGoals, _) ← highlightGoals ci goals |>.run ⟨ids, false, suppressNamespaces⟩ |>.run infoTable |>.run .empty
  pure hlGoals
