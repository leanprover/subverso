/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

example : ∃ n : Nat, n = n → True := by
  refine ⟨?n, ?_⟩
  rotate_left
--^ PROOF_STATE: pendingWitness
  intro h
--^ PROOF_STATE: pendingHyp
  case n => exact 3
  skip
--^ PROOF_STATE: assignedHyp
  trivial

example : Nat → Nat → True := by
  intro h
--^ PROOF_STATE: hypFirst
  intro h
--^ PROOF_STATE: hypShadowed
  trivial

example (x : id Nat) (h : x = x) : x = x := by
  dsimp only [id] at x
--^ PROOF_STATE: hypTypeChanged
  exact h

example : ∃ n : Nat, n = n := by
  refine ⟨?n, ?_⟩
  first
    | case n => exact 1
      skip
------^ PROOF_STATE: firstBranch
      fail
    | case n => exact 2
      skip
------^ PROOF_STATE: secondBranch
  rfl

example : ∃ n : Nat, n = n := by
  refine ⟨?n, ?_⟩
  rotate_left
  skip
--^ PROOF_STATE: taggedGoal
  case n =>
    skip
----^ PROOF_STATE: untaggedGoal
    exact 1
  rfl
