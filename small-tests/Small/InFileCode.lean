/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Elab.Term
import Lean.Elab.Command

/-!
This test defines a function, a structure with a derived instance, macros, elaborators, an
unexpander and tactics. All are used in the file itself. This makes sure that changes to
elaboration/highlighting don't break running code in the same file.
-/

open Lean Elab

def double (n : Nat) : Nat := n * 2

#eval double 21

structure Point where
  x : Nat
  y : Nat
deriving Repr

#eval ({ x := 1, y := double 2 } : Point)

macro "twice! " t:term : term => `(($t) + ($t))

#eval twice! 5

elab "lengthOf! " s:str : term => return mkNatLit s.getString.length

#eval lengthOf! "hello"

elab "#say " s:str : command => logInfo s.getString

#say "in-file command"

def wrap (n : Nat) : Nat := n

syntax "⟪" term "⟫" : term

macro_rules
  | `(⟪$n⟫) => `(wrap $n)

@[app_unexpander wrap] def unexpandWrap : PrettyPrinter.Unexpander
  | `($_ $n) => `(⟪$n⟫)
  | _ => throw ()

#check wrap 3

macro "my_trivial" : tactic => `(tactic| first | rfl | trivial)

example : double 2 = 4 := by my_trivial

elab "my_rfl" : tactic => do Tactic.evalTactic (← `(tactic| rfl))

example : ⟪double 3⟫ = 6 := by my_rfl
