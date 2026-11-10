/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
structure S where
  n : Nat
def S.get (s : S) : Nat := s.n
theorem getEq (s : S) : s.get = s.n := rfl
example (s : S) : s.get = s.n := getEq s
attribute [pp_nodot] S.get
example (s : S) : s.get = s.n := getEq s
