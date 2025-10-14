/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Examples.Messages.NormalizeLineNum
import SubVerso.Examples.Messages.NormalizeMetavars

namespace SubVerso.Examples.Messages

/--
Compares info and errors modulo leading and trailing whitespace to work around `#eval` always
sticking a \n at the end plus trailing spaces, and with normalized metavars and recursion issue line
numbers to make comparisons less fragile.
-/
def messagesMatch (msg1 msg2 : String) : Bool :=
  let msg1 := normalizeLineNums <| normalizeMetavars msg1
  let msg2 := normalizeLineNums <| normalizeMetavars msg2
  let lines1 := msg1.split (· == '\n') |>.map (·.trimRight) |>.reverse |>.dropWhile String.isEmpty |>.reverse
  let lines2 := msg2.split (· == '\n') |>.map (·.trimRight) |>.reverse |>.dropWhile String.isEmpty |>.reverse
  lines1 == lines2
