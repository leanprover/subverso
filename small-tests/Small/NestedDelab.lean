/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean
open Lean PrettyPrinter Delaborator SubExpr Meta

def MySet (α : Type u) := α → Prop

instance : LE (MySet α) := ⟨fun s t => ∀ a, s a → t a⟩

class SetLike (α : Type u)

instance : SetLike (MySet α) := ⟨⟩

@[delab app.LE.le]
def delabSetLe : Delab := do
  let e ← getExpr
  guard <| e.getAppNumArgs == 4
  guard <| (← trySynthInstance (← mkAppM ``SetLike #[e.getArg! 0])) matches .some _
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  `($x ≤ $y)

example {α : Type} (s : MySet α) (h : ∀ u : MySet α, s ≤ u) : True := trivial
