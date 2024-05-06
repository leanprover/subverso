-- This module serves as the root of the `Demo` library.
-- Import modules here that should be built as part of the library.
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
