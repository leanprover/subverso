/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Data.Json
import Lean.Data.Position
import Lean.Syntax
import Lean.Elab.Command
import SubVerso.Compat
import SubVerso.Examples.Slice.Attribute

open Lean (SourceInfo Syntax Environment FileMap MonadEnv MonadError MonadFileMap getFileMap getEnv nullKind)

open SubVerso.Compat (Parsec HashMap)

namespace SubVerso.Examples.Slice

open Attribute

private def takeComments (ws : Substring) : Array (SourceInfo × Substring) := Id.run do
  let mut iter : String.Iterator := ws.toIterator
  let mut leading := iter
  let mut found := #[]
  while iter.pos < ws.stopPos do
    if iter.curr == '-' && iter.hasNext then
      let mut iter' := iter.next
      if iter'.curr == '-' && iter'.hasNext then
        while iter'.pos < ws.stopPos && iter'.curr != '\n' do
          iter' := iter'.next
        let l := ⟨ws.str, leading.pos, iter.pos⟩
        let t := ⟨ws.str, iter'.pos, iter'.pos⟩
        found := found.push ((.original l iter.pos t iter'.pos), ⟨iter.s, iter.i, iter'.i⟩)
        iter := iter'
        continue
    else if iter.curr == '/' then
      let mut iter' := iter.next
      if iter'.curr == '-' && iter'.hasNext then
        let mut depth := 1
        while depth > 0 && iter'.pos < ws.stopPos && iter'.hasNext do
          if iter'.curr == '/' && iter'.hasNext then
            iter' := iter'.next
            if iter'.curr == '-' then
              depth := depth + 1
              iter' := iter'.next
          else if iter'.curr == '-' && iter'.hasNext then
            iter' := iter'.next
            if iter'.curr == '/' then
              depth := depth - 1
              iter' := iter'.next
          else
            iter' := iter'.next
        let l := ⟨ws.str, leading.pos, iter.pos⟩
        let t := ⟨ws.str, iter'.pos, iter'.pos⟩
        found := found.push ((.original l iter.pos t iter'.pos), ⟨iter.s, iter.i, iter'.i⟩)
        iter := iter'
    else
      iter := iter.next
  found

private def commentString (str : Substring) : Substring :=
  if str.take 2 == "--".toSubstring then str.drop 2
  else str.drop 2 |>.dropRight 2

private structure SliceCommand where
  begin : Bool
  kind : String
  commentAt : String.Range
deriving Repr

private def SliceCommand.beginRange := SliceCommand.mk true
private def SliceCommand.endRange := SliceCommand.mk false

open SubVerso.Compat.Parsec String in
private def sliceCommand (range : String.Range) : Parsec SliceCommand := do
  ws
  skipString "!!"
  ws
  beginCmd <|> endCmd
where
  nameChar (c : Char) := c.isAlphanum || c == '_'
  done : Parsec Unit := fun iter =>
    if iter.pos ≥ range.stop then .success iter ()
    else .error iter "Expected finished comment"
  beginCmd := do
    skipString "begin"
    skipChar ' '
    ws
    let name ← many1Chars (satisfy nameChar)
    ws
    _ ← optional <| skipString "-/"
    done
    pure <| .beginRange name range
  endCmd := do
    skipString "end"
    skipChar ' '
    ws
    let name ← many1Chars (satisfy nameChar)
    ws
    _ ← optional <| skipString "-/"
    done
    pure <| .endRange name range


private partial def getComments : Syntax → Array (SourceInfo × Substring × Option SliceCommand)
  | .atom si _str => ws si
  | .ident si _str _x _ => ws si
  | .node si _k sub =>
    sub.foldr (fun a b => getComments a ++ b) (ws si)
  | .missing => #[]
where
  ws
    | .original leading _ trailing _ =>
      (takeComments leading ++ takeComments trailing).map fun (si, str) =>
        let iter := commentString str |>.toIterator
        match si with
        | .original _ b _ e =>
          match sliceCommand ⟨b, e⟩ iter with
          | .error _iter _msg =>
            (si, str, none)
          | .success _ v => (si, str, some v)
        | _ => (si, str, none)
    | _ => #[]


/--
Returns `true` if `stx`'s source span is definitely included in `rng`.

Returns false in the following circumstances:
 * No range can be found for the syntax
 * A range is found, but it exceeds rng in one or both directions or does not overlap it
-/
private def syntaxIn (stx : Syntax) (rng : String.Range) : Bool :=
  if let some sr := stx.getRange? then
    rng.includes sr
  else
    false

private partial def removeRanges (env : Environment) (rngs : Array String.Range) (stx : Syntax) : Syntax :=
  match stx with
  | .atom .. | .ident .. | .missing => stx
  | .node info kind subs => Id.run do
    if rngs.size > 0 then
      let slicers ← slicersInEnv env kind

      for s in slicers do
        if let some stx' := s (removeRanges env rngs) (.node info kind subs) rngs then
          return stx'

      -- Fallback if no special-purpose slicers apply
      let newSubs ← subs.filter (fun s => !rngs.any (syntaxIn s)) |>.map (removeRanges env rngs)

      -- If there were atoms in the original tree and only one non-atom subtree remains, replace the surrounding node
      -- This catches situations like
      --    x /- !! begin foo  -/ + 3 /- !! end foo -/
      -- which should become just x.
      if h : subs.any (· matches .atom ..) ∧ subs.size > 1 ∧ newSubs.size = 1 ∧ newSubs[0]? matches some (Syntax.node ..) then
        pure <| newSubs[0]'(by cases h; simp_arith [*])
      else
        pure <| .node info kind newSubs
    else pure stx

private def getSlices (slices : Array SliceCommand) : Except String (HashMap String (Array String.Range)) := do
  let mut opened : HashMap String (String.Pos) := {}
  let mut closed : HashMap String (Array String.Range) := {}
  for s in slices do
    match s with
    | .beginRange name rng =>
      if opened.contains name then .error s!"Slice '{name}' opened twice"
      else opened := opened.insert name rng.stop
    | .endRange name pos =>
      if let some p := opened[name]? then
        closed := closed.insert name <| closed.getD name #[] |>.push ⟨p, pos.start⟩
        opened := opened.erase name
      else .error s!"Slice '{name}' not open"
  pure closed

private partial def removeSliceComments (slices : Array SliceCommand) (fileMap : FileMap) : Syntax → Syntax
  | .atom si str => .atom (remFromSourceInfo si) str
  | .ident si str n pres => .ident (remFromSourceInfo si) str n pres
  | .missing => .missing
  | .node si k sub => .node (remFromSourceInfo si) k (sub.map (removeSliceComments slices fileMap))
where
  remFromSourceInfo : SourceInfo → SourceInfo
    | .original leading b trailing e =>
      .original (remFromSubstring leading) b (remFromSubstring trailing) e
    | other => other
  getRange : Substring → String.Range
    | ⟨_, b, e⟩ => ⟨b, e⟩
  remFromSubstring (str : Substring) : Substring := Id.run do
    -- Not just an optimization - some parsers use empty strings that aren't build as substrings
    -- of the original source
    if str.str.isEmpty then return str
    if str.str != fileMap.source then panic! "Mismatched strings"
    let mut found := false
    let mut start := str.startPos
    let mut newStr := ""
    for s in slices do
      if getRange str |>.includes s.commentAt then
        found := true
        -- If the characters on the same line as the start and end of the comment are all whitespace,
        -- delete whole lines; otherwise, delete just the comment's range
        let startPos := fileMap.toPosition s.commentAt.start
        let startLine := fileMap.positions[startPos.line - 1]!
        let preComment := fileMap.source.extract startLine s.commentAt.start

        let endPos := fileMap.toPosition s.commentAt.stop
        let endLine := fileMap.positions[endPos.line]!
        let postComment := fileMap.source.extract s.commentAt.stop endLine
        let deleteLines := preComment.all Char.isWhitespace && postComment.all Char.isWhitespace

        if deleteLines then
          newStr := fileMap.source.extract start startLine
          start := endLine
        else
          newStr := fileMap.source.extract start s.commentAt.start
          start := s.commentAt.stop

    newStr := newStr ++ fileMap.source.extract start str.stopPos
    if found then newStr.toSubstring else str

structure Slices where
  original : Syntax
  residual : Syntax
  sliced : HashMap String Syntax

def sliceSyntax [Monad m] [MonadEnv m] [MonadError m] [MonadFileMap m] (stx : Syntax) : m Slices := do
  let commands := getComments stx |>.filterMap (fun (_, _, cmd?) => cmd?)
  let ss ←
    match getSlices commands with
    | .ok ss => pure ss
    | .error m => throwError m

  let stx' := removeSliceComments commands (← getFileMap) stx
  let env ← getEnv
  let mut sliced : HashMap String Syntax := {}
  for (s, _) in ss.toArray do
    let rem := ss.erase s |>.toList |>.flatMap (·.snd.toList) |>.toArray
    sliced := sliced.insert s (removeRanges env rem stx')
  let residual := removeRanges env (ss.toList.flatMap (·.snd.toList) |>.toArray) stx'

  return {original := stx, residual, sliced}

namespace Syntax


@[slicer null]
def null : Slicer := fun go stx rngs => do
  let .node si k subs := stx
    | none
  let newSubs := subs.filter (fun s => !rngs.any (syntaxIn s)) |>.map go
  -- Don't apply the heuristic for null nodes
  return .node si k newSubs

@[slicer Lean.Parser.Tactic.tacticSeq1Indented]
def tacticSeq1Indented : Slicer := fun go stx rngs => do
  let .node si k #[.node si' k' subs] := stx
    | none
  let mut out : Array Syntax := #[]
  let mut i := 0
  while h : i < subs.size do
    if !rngs.any (syntaxIn subs[i]) then
      out := out.push (go subs[i])
      if h' : i + 1 < subs.size then
        out := out.push subs[i+1]
      else
        out := out.push (.node SourceInfo.none nullKind #[])
    i := i + 2
  -- Pop the resulting array because the loop pushes an extraneous null separator node onto the end
  return .node si k #[.node si' k' out.pop]
