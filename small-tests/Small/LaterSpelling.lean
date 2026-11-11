/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
theorem maxBeforeSpelling (a b : Nat) : max a b = max a b := by
  rfl

#check max 1 2

recommended_spelling "maximum" for "max" in [Max.max]

theorem maxAfterSpelling (a b : Nat) : max a b = max a b := by
  rfl

#check max 3 4
