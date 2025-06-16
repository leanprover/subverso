
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
--  ^ PROOF_STATE: A
--       ^ PROOF_STATE: A'
--          ^ PROOF_STATE: A''
--            ^ PROOF_STATE: A'''
  | inr hq => apply Or.inl; exact hq
--  ^ PROOF_STATE: B
--       ^ PROOF_STATE: B'
--          ^ PROOF_STATE: B''
--            ^ PROOF_STATE: B'''

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp | inr hq =>
--                  ^ PROOF_STATE: Arr
--  NB: The highlighting of multi-arm LHSes was missing in Lean prior to 4.14, so the
--  tests don't currently check it. It would be better to version-case this.
    simp [*]
--  ^ PROOF_STATE: Two
