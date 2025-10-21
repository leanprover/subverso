/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Lean.Parser.Command
import Lean.Environment
import Lean.Elab.Command
public import Lean.Data.Options

import SubVerso.Compat
import SubVerso.Highlighting.Code
public import SubVerso.Examples.Env
public section

/-!
This module contains a version of the signature checking code that's independent of the embedded
example infrastructure. In the long run, this version should replace it, and we should migrate away
from the old name example mechanism in favor of quotations from the anchor mechanism.
-/

open Lean Elab Command Term

open SubVerso.Highlighting

namespace SubVerso.Examples

def getSuppressed [Monad m] [MonadOptions m] : m (List Name) := do
  return (← getOptions) |> SubVerso.examples.suppressedNamespaces.get |>.splitOn " " |>.map (·.toName)

private def biDesc : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .instImplicit => "instance"
  | .strictImplicit => "strict implicit"

private partial def compare (blame : Syntax): Expr → Expr → MetaM Unit
  | .forallE x t1 b1 bi1, .forallE y t2 b2 bi2 => do
    if x.eraseMacroScopes != y.eraseMacroScopes then
      logErrorAt blame m!"Mismatched parameter name: expected '{x.eraseMacroScopes}' but got '{y.eraseMacroScopes}'"
    if bi1 != bi2 then logErrorAt blame m!"Mismatched binder of {x}: expected {biDesc bi1} but got {biDesc bi2}"
    if t1.isAppOfArity' ``optParam 2 then
      if t2.isAppOfArity' ``optParam 2 then
        if !(← Meta.isDefEq t1.appArg! t2.appArg!) then
          logErrorAt blame m!"Mismatched default values for parameter {x}: expected '{t1.appArg!}' but got '{t2.appArg!}'"
    Meta.withLocalDecl x bi1 t1 fun e =>
      compare blame (b1.instantiate1 e) (b2.instantiate1 e)
  | .mdata _ tty', sty => compare blame tty' sty
  | tty , .mdata _ sty' => compare blame tty sty'
  | _, _ => pure ()

/--
Check the signature by elaborating and comparing.
-/
def checkSignature
    (sigName : TSyntax ``Lean.Parser.Command.declId)
    (sig : TSyntax ``Lean.Parser.Command.declSig) :
    CommandElabM (Highlighted × String × Compat.String.Pos × Compat.String.Pos) := do
  let sig : TSyntax `Lean.Parser.Command.declSig := ⟨sig⟩

  -- First make sure the names won't clash - we want two different declarations to compare.
  let mod ← getMainModule
  let sc ← getCurrMacroScope
  let addScope x := mkIdentFrom x (addMacroScope mod x.getId sc)
  let declName ← match sigName with
    | `(Lean.Parser.Command.declId|$x:ident) => pure x
    | `(Lean.Parser.Command.declId|$x:ident.{$_u:ident,*}) => pure x
    | _ => throwErrorAt sigName "Unexpected format of name: {sigName}"
  let (target, targetTrees) ← do
    let origTrees ← getResetInfoTrees
    let mut tgtTrees := PersistentArray.empty
    try
      let name ← liftTermElabM (Compat.realizeNameNoOverloads declName)
      tgtTrees ← getInfoTrees
      pure (name, tgtTrees)
    finally
      modifyInfoState ({· with trees := origTrees ++ tgtTrees})

  let noClash ← match sigName with
    | `(Lean.Parser.Command.declId|$x:ident) => `(Lean.Parser.Command.declId| $(addScope x):ident)
    | `(Lean.Parser.Command.declId|$x:ident.{$u:ident,*}) => `(Lean.Parser.Command.declId| $(addScope x):ident.{$u,*})
    | _ => throwErrorAt sigName "Unexpected format of name: {sigName}"

  -- Elaborate as an opaque constant (unsafe is to avoid an Inhabited constraint on the return type)
  let stx ← `(command| noncomputable unsafe opaque $noClash $sig)
  let trees ← withoutModifyingEnv do
    let origTrees ← getResetInfoTrees
    let mut outTrees := PersistentArray.empty
    try
      elabCommand stx
      outTrees ← getInfoTrees
      if ← MonadLog.hasErrors then
        let errs := (← get).messages.toList.filter (·.severity matches .error)
        let errs ← errs.mapM fun m => m.toString
        throwErrorAt sigName "Failed to elaborate signature. Errors:{m!"and".joinSep errs}"

      -- The "source" is what the user wrote, the "target" is the existing declaration
      let source ← liftTermElabM <| Compat.realizeNameNoOverloads (addScope declName)
      let ti ← getConstInfo target
      let si ← getConstInfo source
      if si.numLevelParams != ti.numLevelParams then
        throwErrorAt sigName "Mismatched number of level params: {target} has {ti.numLevelParams}, not {si.numLevelParams}"
      let lvls := ti.levelParams.map mkLevelParam
      let te : Expr := .const target lvls
      let se : Expr := .const source lvls
      liftTermElabM do
        let tty ← Meta.inferType te
        let sty ← Meta.inferType se
        if !(← Meta.isDefEq tty sty) then
          throwErrorAt sig "Expected {tty}, got {sty}"
        compare sigName tty sty
      pure outTrees
      finally
        modifyInfoState ({· with trees := origTrees ++ outTrees})

  -- Now actually generate the highlight
  let .original leading startPos _ _ := sigName.raw.getHeadInfo
    | throwErrorAt sigName "Failed to get source position"
  let .original _ _ trailing stopPos := sig.raw.getTailInfo
    | throwErrorAt sig.raw "Failed to get source position"
  let text ← getFileMap
  let suppressedNS ← getSuppressed
  let str := Compat.String.Pos.extract text.source leading.startPos trailing.stopPos
  let trees := targetTrees ++ trees
  let hl ← liftTermElabM <| withDeclName `x do
    pure <| .seq #[← highlight sigName #[] trees suppressedNS, ← highlight sig #[] trees suppressedNS]


  return (hl, str, startPos, stopPos)
