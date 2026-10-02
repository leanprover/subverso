/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import «Demo».Basic

-- ANCHOR: version
#eval Lean.versionString
-- ANCHOR_END: version

-- ANCHOR: proof
theorem test (n : Nat) : n * 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    simp
-- ANCHOR_END: proof

-- ANCHOR: proofWithInstance
-- Test that proof states containing daggered names can round-trip
def test2 [ToString α] (x : α) : Decidable (toString x = "") := by
  constructor; sorry
-- ANCHOR_END: proofWithInstance

-- ANCHOR: hasSorry
theorem bogus : 2 = 2 := by sorry
-- ANCHOR_END: hasSorry

-- ANCHOR: linted
def g : α → Nat
  | x => 3
-- ANCHOR_END: linted
