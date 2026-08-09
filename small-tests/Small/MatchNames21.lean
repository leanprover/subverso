theorem mySubst {p : Nat → Prop} : x = y → p x → p y
  | rfl, h => h

#check @mySubst.match_1_1

theorem twoPlusTwo : 2 + 2 = 4 := by
  rfl
--^ PROOF_STATE: matchRfl
