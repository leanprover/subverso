/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import SubVerso.Highlighting.Highlighted
public import SubVerso.Compat
public section

namespace SubVerso.Highlighting

/--
If a comment could be an anchor indicator, returns the anchor's name along with `true` for a start
and `false` for an end.

An anchor consists of a line comment that contains `ANCHOR:` or `ANCHOR_END:` followed by the name
of the anchor.
-/
def anchor? (line : String) : Except String (String × Bool) := do
  let mut line := line.trim
  unless line.startsWith "--" do throw "Not a comment"
  line := line.dropWhile (· == '-')
  line := line.trimLeft
  if line.startsWith "ANCHOR:" then
    line := line.stripPrefix "ANCHOR:"
    line := line.trimLeft
    if line.isEmpty then throw "Expected line number after `ANCHOR: `" else return (line, true)
  else if line.startsWith "ANCHOR_END:" then
    line := line.stripPrefix "ANCHOR_END:"
    line := line.trimLeft
    if line.isEmpty then throw "Expected line number after `ANCHOR_END: `" else return (line, false)
  else throw s!"Expected `ANCHOR:` or `ANCHOR_END:`, got {line}"


/--
If a comment could be a proof state indicator, returns the state's name and the indicated column.

A proof state indicator consists of a line that contains a position and a name. The position is a
caret, and the name is `PROOF_STATE:` followed by the state's name.
-/
def proofState? (line : String) : Except String (String × Nat) := do
  let mut line := line.toSubstring
  let mut column : Nat := 0
  let mut caret : Option Nat := none
  let mut name : Option String := none
  -- First drop leading whitespace
  let ws := line.takeWhile (·.isWhitespace) |>.toString
  column := column + ws.length
  line := line.drop ws.length

  -- Drop comment marker
  let some content := line.dropPrefix? "--".toSubstring
    | throw "Not a line comment"
  column := column + 2
  line := content
  while !line.isEmpty && line.get 0 == '-' do
    column := column + 1
    line := line.drop 1

  while !line.isEmpty && line.get 0 ≠ '\n' do
    -- Drop whitespace until caret or tag is found
    while !line.isEmpty && line.get 0 == ' ' do
      column := column + 1
      line := line.drop 1

    if !line.isEmpty && line.get 0 == '^' then
      if caret.isSome then throw "Redundant position marker `^`"
      else caret := some column
      column := column + 1
      line := line.drop 1
    else if let some afterState := line.dropPrefix? "PROOF_STATE:".toSubstring then
      column := column + "PROOF_STATE:".length
      line := afterState
      while !line.isEmpty && line.get 0 == ' ' do
        column := column + 1
        line := line.drop 1
      if line.isEmpty then throw "Expected proof state name after `PROOF_STATE:`"
      if line.get 0 |>.isAlpha then
        if name.isSome then throw "Proof state name already registered"
        let n := line.takeWhile (fun c => c.isAlphanum || c == '\'') |>.toString
        name := some n
        column := column + n.length
        line := line.drop n.length
    else if line.isEmpty then break
    else
      throw "Expected `PROOF_STATE:` or `^`"

  if let some n := name then
    if let some c := caret then
      return (n, c)
    else throw "No position marker (`^`) found"
  else throw "No name indicated"

namespace Highlighted
open SubVerso.Compat (HashMap)

/--
“Normalize” highlighted code, merging adjacent text and sequence elements.
-/
private partial def normHl : Highlighted → Highlighted
  | .seq xs => xs.map normHl |>.foldl (init := .empty) .append
  | hl@(.point ..) => hl
  | .tactics x y z m => .tactics x y z (normHl m)
  | .span x y => .span x (normHl y)
  | .text "" => .empty
  | .text s => .text s
  | .token t => .token t
  | .unparsed s => .unparsed s

open Highlighted in
private inductive HlCtx where
  | tactics (info : Array (Goal Highlighted)) (startPos endPos : Nat)
  | span (info : Array Message)
deriving Repr

private def HlCtx.wrap (ctx : HlCtx) (hl : Highlighted) : Highlighted :=
  match ctx with
  | .tactics info start stop => .tactics info start stop hl
  | .span info => .span (info.map fun x => (x.1, x.2)) hl

private structure Hl where
  here : Highlighted
  context : Array (Highlighted × HlCtx)
deriving Inhabited

private def Hl.empty : Hl where
  here := .empty
  context := #[]

private def Hl.isEmpty (hl : Hl) : Bool :=
  hl.here.isEmpty && hl.context.all (·.1.isEmpty)

private def Hl.close (hl : Hl) : Hl :=
  match hl.context.back? with
  | none => hl
  | some (left, .tactics info s e) => { hl with
    here := left ++ .tactics info s e hl.here,
    context := hl.context.pop
  }
  | some (left, .span info) => { hl with
    here := left ++ .span (info.map fun x => (x.1, x.2)) hl.here,
    context := hl.context.pop
  }

private def Hl.open (ctx : HlCtx) (hl : Hl) : Hl where
  here := .empty
  context := hl.context.push (hl.here, ctx)

private def Hl.toHighlighted (hl : Hl) : Highlighted :=
  hl.context.foldr (init := hl.here) fun
    | (left, .tactics info startPos endPos), h => left ++ .tactics info startPos endPos h
    | (left, .span info), h => left ++ .span (info.map fun x => (x.1, x.2)) h

private instance : HAppend Hl Highlighted Hl where
  hAppend hl h :=
    { hl with
      here := hl.here ++ h
    }

private instance : HAppend Hl String Hl where
  hAppend hl s := HAppend.hAppend hl (Highlighted.text s)

def Internal.getLines (str : String) : Array String := Id.run do
  let mut iter := str.iter
  let mut lines := #[]
  let mut here := ""
  while h : iter.hasNext do
    let c := iter.curr' h
    iter := iter.next' h
    here := here.push c
    if c == '\n' then
      lines := lines.push here
      here := ""
  return lines.push here

private def Hl.tacticsAt? (hl : Hl) (column : Nat) : Option Highlighted := do
  let mut context : Array (Highlighted × HlCtx × Highlighted) := hl.context.map fun (l, c) => (l, c, .empty)

  let mut left : Highlighted := .empty
  let mut focus : Highlighted := hl.here
  -- The current line, as accumulated so far
  let mut right : Highlighted := .empty

  repeat
    match focus with
    | .seq xs =>
      if let some last := xs.back? then
        left := left ++ .seq xs.pop
        focus := last
      else if left.isEmpty then -- pop the stack or terminate the loop
        if let some (l', f, r') := context.back? then
          right := f.wrap right ++ r'
          focus := l'
          left := .empty
          context := context.pop
        else
          break -- ran out of document, so line beginning found
      else -- move
        focus := left
        left := .empty
    | .tactics info start stop x =>
      context := context.push (left, .tactics info start stop, right)
      left := .empty
      right := .empty
      focus := x
    | .span info x =>
      context := context.push (left, .span (info.map fun x => ⟨x.1, x.2⟩), right)
      left := .empty
      right := .empty
      focus := x
    | .text s | .unparsed s =>
      let lines := Internal.getLines s
      if lines.size > 1 then -- found a line break
        right := .text (Compat.Array.back! lines) ++ right
        repeat
          if let some (_, f, r') := context.back? then
            right := f.wrap right ++ r'
            context := context.pop
          else break
        break
      else
        right := focus ++ right
        focus := left
        left := .empty
    | .point .. | .token .. =>
      right := focus ++ right
      focus := left
      left := .empty

  -- At this point, `right` contains the line. Now find the most specific tactics at the provided column.
  let mut column := column -- Counts down to 0 - how many columns need to be traversed to find the state?
  let mut answer? := none

  -- The line can contain two things: .inl represents a next element of text to consider, while .inr
  -- represents a prior answer to restore.
  let mut line : List (Highlighted ⊕ Option Highlighted) := [.inl right]

  repeat
    match line with
    | [] => break
    | x :: more =>
      match x with
      | .inr ans =>
        answer? := ans
        line := more
      | .inl hl =>
        match hl with
        | .seq xs =>
          line := xs.toList.map .inl ++ more
        | .text s | .token ⟨_, s⟩ | .unparsed s =>
          if s.length > column then
            break
          else
            column := column - s.length
            line := more
        | .point .. =>
          line := more
        | .span _info x =>
          line := .inl x :: more
        | .tactics _info _start _stop x =>
          line := .inl x :: .inr answer? :: more
          answer? := hl

  answer?

/--
The examples that were extracted via special comment syntax.
-/
structure AnchoredExamples where
  /--
  The code, with processed anchor instructions removed
  -/
  code : Highlighted
  /--
  The contents of named anchors. Maps
  ```
  -- ANCHOR: Y
  code
  -- ANCHOR_END: Y
  ```
  to
  ```
  `Y ↦ code
  ```
  -/
  anchors : HashMap String Highlighted
  /--
  The named proof states.
  -/
  proofStates : HashMap String Highlighted

/--
Extracts code from rendered examples based on comment directives.

There are two kinds of extracted code: anchors and named proof states. Anchors name one or more
lines of code:
```
-- ANCHOR: Y
code
-- ANCHOR_END: Y
```
All anchors that are started must be terminated, and anchor names may not be repeated. Proof states
are named via comments like this:
```
...      := by
  ...
  induction x
--   ^   PROOF_STATE: X
```
or
```
...      := by
  ...
   simp [x, y, z, w, foo]
-- PROOF_STATE: X  ^
```
where the '^' points at the location of the proof state.

Passing `false` for `textAnchors` or `proofStates` disables processing of the corresponding anchor types.
-/
def anchored (hl : Highlighted) (textAnchors := true) (proofStates := true) : Except String AnchoredExamples := do
  let mut anchorOut : HashMap String Highlighted := {}
  let mut tacOut : HashMap String Highlighted := {}
  let mut openAnchors : HashMap String Hl := {}
  let mut doc : Hl := .empty
  let mut todo := [some (normHl hl)]
  let mut ctx : Array HlCtx := #[]
  repeat
    match todo with
    | [] => break
    | none :: hs =>
      todo := hs
      ctx := ctx.pop
      openAnchors := openAnchors.map fun _ h => h.close
      doc := doc.close
    | some (.text s) :: hs =>
      -- It's most robust to only search for proof states before adding newlines to the current set
      -- of comments, in case proof state indicator comments are mixed up with other kinds of
      -- comments.
      let preText := doc
      todo := hs
      let lines := Internal.getLines s
      for line in lines do
        match guard textAnchors *> (anchor? line |>.toOption) with
        | none =>
          match guard proofStates *> (proofState? line |>.toOption) with
          | none =>
            openAnchors := openAnchors.map fun _ hl => hl ++ line
            doc := doc ++ line
          | some (p, c) =>
            if let some t := preText.tacticsAt? c then
              if tacOut.get? p |>.isSome then throw s!"Proof state already found: '{p}'"
              tacOut := tacOut.insert p t
            else
              throw s!"No proof state at column {c} for '{p}'"
        | some (a, true) =>
          if openAnchors.contains a then throw s!"Anchor already opened: {a}"
          if anchorOut.contains a then throw s!"Anchor already used: {a}"
          openAnchors := openAnchors.insert a {
            here := .empty
            context := ctx.map (.empty, ·)
          }
        | some (a, false) =>
          if let some hl := openAnchors.get? a then
            anchorOut := anchorOut.insert a hl.toHighlighted
            openAnchors := openAnchors.erase a
          else throw s!"Anchor not open: {a}"
    | some h@(.token ..) :: hs | some h@(.point ..) :: hs | some h@(.unparsed ..) :: hs =>
      todo := hs
      openAnchors := openAnchors.map fun _ hl => hl ++ h
      doc := doc ++ h
    | some (.seq xs) :: hs =>
      todo := xs.toList.map some ++ hs
    | some (.tactics info startPos endPos x) :: hs =>
      ctx := ctx.push (.tactics info startPos endPos)
      todo := some x :: none :: hs
      openAnchors := openAnchors.map fun _ hl => hl.open (.tactics info startPos endPos)
      doc := doc.open (.tactics info startPos endPos)
    | some (.span info x) :: hs =>
      let info := info.map fun x => ⟨x.1, x.2⟩
      ctx := ctx.push (.span info)
      todo := some x :: none :: hs
      openAnchors := openAnchors.map fun _ hl => hl.open (.span info)
      doc := doc.open (.span info)
  if openAnchors.isEmpty then return ⟨doc.toHighlighted , anchorOut, tacOut⟩
  else throw s!"Unclosed anchors: {", ".intercalate openAnchors.keys}"

private def dropPrefix? (iter : String.Iterator) (s : String) : Option String.Iterator := Id.run do
  let mut iter := iter
  let mut iter' := s.iter
  while h : iter.hasNext ∧ iter'.hasNext do
    if iter.curr' h.1 ≠ iter'.curr' h.2 then return none
    iter := iter.next
    iter' := iter'.next
  if iter'.hasNext then return none
  return (some iter)

def Internal.isAnchorLike (str : String) : Bool := Id.run do
  let mut iter := str.iter
  while iter.hasNext do
    iter := iter.find fun c => c == 'A' || c == 'P'
    if let some i := dropPrefix? iter "ANCHOR" then
      iter := i
      if dropPrefix? iter ":" |>.isSome then return true
      if dropPrefix? iter "_END:" |>.isSome then return true
    else iter := iter.next -- this A or P didn't work out
  return false

def Internal.isStateLike (str : String) : Bool := Id.run do
  let mut iter := str.iter
  while iter.hasNext do
    iter := iter.find fun c => c == 'A' || c == 'P'
     if dropPrefix? iter "PROOF_STATE:" |>.isSome then return true
    else iter := iter.next -- this A or P didn't work out
  return false
