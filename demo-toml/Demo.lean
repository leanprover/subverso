/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import «Demo».Basic

import SubVerso.Examples

open SubVerso.Examples

%example version
#eval Lean.versionString
%end

%example xdef
def f (x : Nat) := %ex{add}{33 + %ex{X}{x}}
%end

%example proof
theorem test (n : Nat) : n * 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    simp
%end

%example proofWithInstance
-- Test that proof states containing daggered names can round-trip
def test2 [ToString α] (x : α) : Decidable (toString x = "") := by
  constructor; sorry
%end

%show_name Nat.rec

%signature qs
  Array.qsort.{u} {α : Type u} (as : Array α) (lt : α → α → Bool) (low : Nat := 0) (high : Nat := as.size - 1) : Array α

%example hasSorry
theorem bogus : 2 = 2 := by sorry
%end
