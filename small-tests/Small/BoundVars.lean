/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
variable (R : Type)

example (s : R → Prop) (h : ∀ a b c d e f g i j k : R, s a) : ∀ a b c d e f g i j k : R, s a := by
  skip
  exact h

example (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ : R) : x₁ = x₁ := rfl
