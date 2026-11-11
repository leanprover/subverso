/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

example : ∀ (n : Nat), n = n → ∀ (n : Nat), n = n → True := by
  intro n h
--^ PROOF_STATE: first
  intro n h'
--^ PROOF_STATE: shadowed
  trivial

def shadowingBinderProp (n : Nat) : Prop := ∀ x : Nat, x + n = n + x

example (x : Nat) (h : shadowingBinderProp x) : ∀ (x_1 : Nat), x_1 = x_1 := by
  unfold shadowingBinderProp at h
--^ PROOF_STATE: binderRenamed
  intro x_1
--^ PROOF_STATE: binderRenamedAgain
  rfl

example : (∀ a : Nat, a = a) → (∀ b : Nat, b = b) → True := by
  intro h₁ h₂
--^ PROOF_STATE: alphaEquivalent
  trivial

example : ∀ (α : Type) (P : α → Prop) (a : α), P a → ∀ (α : Type), α = α := by
  intro α P a h
--^ PROOF_STATE: hoverTypes
  intro α
--^ PROOF_STATE: hoverTypesShadowed
  rfl

def shadowingConst : Nat := 1

example (h : shadowingConst = 1) : ∀ (shadowingConst : Nat), shadowingConst = shadowingConst := by
  intro shadowingConst
--^ PROOF_STATE: constShadowed
  rfl
