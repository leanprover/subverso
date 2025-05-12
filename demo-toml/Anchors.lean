/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

-- ANCHOR: NatList
inductive NatList where
  | nil
  --ANCHOR: cons
  | cons : Nat → NatList → NatList
  --ANCHOR_END: cons
-- ANCHOR_END: NatList

def NatList.append : NatList → NatList → NatList
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (xs.append ys)

theorem NatList.append_assoc : ∀ (xs ys zs : NatList), xs.append (ys.append zs) = (xs.append ys).append zs := by
  intro xs ys
  --^ PROOF_STATE: doubleIntro
  induction xs
  --^ PROOF_STATE: ind
  simp [append]
  --^ PROOF_STATE: base
  simp only [append]
  --^ PROOF_STATE: step
  rename_i ih
  --^ PROOF_STATE: ih
  simp_all
  --^ PROOF_STATE: done
