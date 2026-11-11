/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
def foo (n : Nat) : Nat := n + 1
theorem fooOne : foo 1 = 2 := rfl
example : foo 1 = 2 := fooOne
local notation "F[" n "]" => foo n
example : foo 1 = 2 := fooOne

def bar (n : Nat) : Nat := n
theorem barOne : bar 1 = 1 := rfl
example : bar 1 = 1 := barOne
syntax "⟪" term "⟫" : term
@[app_unexpander bar] def unexpandBar : Lean.PrettyPrinter.Unexpander
  | `($_ $n) => `(⟪$n⟫)
  | _ => throw ()
example : bar 1 = 1 := barOne

def baz (n : Nat) : Nat := n
theorem bazOne : baz 1 = 1 := rfl
section
local notation "Z[" n "]" => baz n
example : baz 1 = 1 := bazOne
end
example : baz 1 = 1 := bazOne

namespace A
def T : Type := Nat
end A
open A
theorem tRefl (x : T) : x = x := rfl
example (x : T) : x = x := tRefl x
def T : Type := Nat
example (x : A.T) : x = x := tRefl x

namespace B
def U : Type := Nat
end B
theorem uRefl (x : B.U) : x = x := rfl
example (x : B.U) : x = x := uRefl x
export B (U)
example (x : B.U) : x = x := uRefl x
