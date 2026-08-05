-- `Small.MatchNames` is deliberately not imported: it references an auxiliary declaration by the
-- name asynchronous elaboration gives it, which only elaborates on toolchains whose compiler
-- elaborates asynchronously (4.19 and later), while this library builds on older toolchains too.
-- The tests extract it directly from source, so it needs no `lake build`.
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
