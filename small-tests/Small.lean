-- This root module builds on every supported toolchain. The tests elaborate `Small.MatchNames19`
-- and `Small.MatchNames21` directly from source, each on the toolchain range whose compiler
-- generates the auxiliary declaration name it references.
import Small.TacticAlts

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp | inr hq =>
    simp [*]
