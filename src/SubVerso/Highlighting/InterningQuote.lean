/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Environment
import Lean.Elab.Command
import Lean.Elab.Deriving.Basic

import SubVerso.Compat

open Lean
open SubVerso

namespace SubVerso.Highlighting

initialize internedStrings : EnvExtension (Compat.HashMap String Name) ←
  Compat.registerEnvExtension (pure {})

private def internString (string : String) : CoreM Name := do
  let strings := internedStrings.getState (← getEnv)
  if let some x := strings.get? string then
    return x
  else withOptions (·.setBool `Elab.async false) do
    let x ← mkAuxName (`SubVerso.InternedStrings ++ (← getEnv).mainModule ++ `string) (hash string).toNat
    let decl := Declaration.defnDecl {
      name := x, levelParams := [], type := Expr.const `String [],
      value := Expr.lit (.strVal string), hints := .abbrev, safety := .safe
    }
    addDecl decl
    compileDecl decl
    modifyEnv (internedStrings.modifyState · (·.insert string x))
    pure x

class InterningQuote (α : Type u) where
  quote : α → CoreM Term

def iquote [InterningQuote α] (x : α) : CoreM Term := InterningQuote.quote x

instance (priority := low) [Quote α] : InterningQuote α where
  quote := pure ∘ Quote.quote

instance : InterningQuote String where
  quote s := do
    let x ← internString s
    return Syntax.mkCApp x #[]

instance [InterningQuote α] : InterningQuote (Option α) where
  quote
    | none => pure <| Syntax.mkCApp ``Option.none #[]
    | some x => (Syntax.mkCApp ``Option.some #[·]) <$> iquote x

instance [InterningQuote α] : InterningQuote (List α) where
  quote := go
where
  go
    | List.nil => pure <| Syntax.mkCApp ``List.nil #[]
    | List.cons x xs => (Syntax.mkCApp ``List.cons #[·, ·]) <$> iquote x <*> go xs

instance [InterningQuote α] : InterningQuote (Array α) where
  quote xs := do
    if xs.size ≤ 8 then
      return Syntax.mkCApp (`Array ++ s!"mkArray{xs.size}".toName) (← xs.mapM iquote)
    else
      let elts ← xs.mapM iquote
      `(#[$elts,*])

instance [InterningQuote α] [InterningQuote β] : InterningQuote (α × β) where
  quote
    | Prod.mk x y => do return Syntax.mkCApp ``Prod.mk #[← iquote x, ← iquote y]

instance [InterningQuote α] [InterningQuote β] : InterningQuote (α ⊕ β) where
  quote
    | .inl x => do return Syntax.mkCApp ``Sum.inl #[← iquote x]
    | .inr y => do return Syntax.mkCApp ``Sum.inr #[← iquote y]

open Lean Elab Command Term
open Lean Parser Term

def deriveIQuote (declNames : Array Name) : CommandElabM Bool := do
  let #[declName] := declNames
    | return false
  let env ← getEnv
  let some (.inductInfo ind) := env.find? declName
    | return false
  if ind.isRec then return false
  let mut branches : Array (TSyntax ``matchAlt) := #[]
  for ctorName in ind.ctors do
    let some (.ctorInfo ci) := env.find? ctorName
      | throwError "'{ctorName}' is not a constructor"
    let mut patvars := #[]
    for i in [0:ci.numParams + ci.numFields] do
      patvars := patvars.push (mkIdent s!"x{i}".toName)
    let lhs := Syntax.mkCApp ctorName patvars
    let rhs := Syntax.mkCApp ``Syntax.mkCApp #[quote ctorName, ← `(#[$[← iquote $patvars],*])]
    let alt ← `(matchAltExpr| | $lhs => do return $rhs)
    branches := branches.push alt
  let cmd ←
    `(instance : InterningQuote $(mkIdent declName) where
        quote x :=
          match x with
          $branches:matchAlt*)
  elabCommand cmd
  return true

initialize
  registerDerivingHandler ``InterningQuote deriveIQuote
