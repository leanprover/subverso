/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Elab.Command
public meta import SubVerso.Highlighting.Anchors.Basic
public section

namespace SubVerso.Highlighting.Highlighted

open Lean in
/--
Checks the anchors in the current file for mistakes such as unclosed `ANCHOR:` segments.
-/
elab "#validate_anchors" : command => do
  let fm ← getFileMap
  let lines := Internal.getLines fm.source
  let mut l : Nat := 0
  let mut report : Array (Nat × String) := #[]
  for line in lines do
    l := l + 1
    let isComment := line.dropWhile (·.isWhitespace) |>.startsWith "--"
    if isComment then
      if Internal.isAnchorLike line then
        match anchor? line with
        | .error e =>
          logError m!"Line {l} didn't parse as anchor command:{indentD <| line.dropRightWhile (· == '\n')}\nError: {e}"
        | .ok (name, status) =>
          report := report.push (l, s!"Anchor {name} {if status then "start" else "end"}")
      if Internal.isStateLike line then
        match proofState? line with
        | .error e =>
          logError m!"Line {l} didn't parse as anchor command:{indentD <| line.dropRightWhile (· == '\n')}\nError: {e}"
        | .ok (name, col) =>
          report := report.push (l, s!"Proof state {name} @ {col}")
  if report.isEmpty then
    logInfo "No anchors or proof states found"
  else
    logInfo <| report.foldl (init := m!"") (fun m (l, s) => m ++ Std.Format.line ++ m!"{l}: {s}")
