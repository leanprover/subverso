/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Elab

open Lean Elab Term

namespace SubVerso.Compat

elab "%first_defined" "[" xs:ident,* "]" : term => do
  let env ← getEnv
  for x in xs.getElems do
    if env.contains x.getId then
      let expr ← elabTerm x none
      return expr
  throwError "None of the names exist"


def realizeNameNoOverloads
    [Monad m] [MonadEnv m] [MonadLiftT CoreM m] [MonadError m]
    [MonadInfoTree m] [MonadResolveName m]
    (ident : Syntax) : m Name :=
  %first_defined [
    Lean.Elab.realizeGlobalConstNoOverloadWithInfo,
    Lean.Elab.resolveGlobalConstNoOverloadWithInfo
  ] ident


elab "%first_succeeding" "[" es:term,* "]" : term <= ty => do
  let mut errs := #[]
  for e in es.getElems do
    try
      let expr ←
        withReader ({· with errToSorry := false}) <|
            elabTermEnsuringType e (some ty)
      let ty' ← Meta.inferType expr
      if ← Meta.isDefEq ty ty' then
        return expr
    catch err =>
      errs := errs.push (e, err)
      continue
  let msgErrs := errs.toList.map fun (tm, msg) => m!"{tm}: {indentD msg.toMessageData}"
  throwError m!"No alternative succeeded. Attempts were: " ++
    indentD (MessageData.joinSep msgErrs Format.line)

open Command in
elab "%if_bound" x:ident cmd:command : command => do
  if (← getEnv).contains x.getId then elabCommand cmd

def importModules (imports : Array Import) (opts : Options) (trustLevel : UInt32 := 0) : IO Environment :=
  Lean.importModules (%first_succeeding [imports, imports.toList]) opts (trustLevel := trustLevel)

def mkRefIdentFVar [Monad m] [MonadEnv m] (id : FVarId) : m Lean.Lsp.RefIdent := do
  pure %first_succeeding [
    .fvar (← getEnv).mainModule id,
    .fvar id
  ]

def refIdentCase (ri : Lsp.RefIdent)
    (onFVar : FVarId → α)
    (onConst : Name → α) : α :=
  %first_succeeding [
    match ri with
    | .fvar _ id => onFVar id
    | .const _ x => onConst x,
    match ri with
    | .fvar id => onFVar id
    | .const x => onConst x
  ]

abbrev Parsec (α : Type) : Type :=
  %first_succeeding [(Lean.Parsec α : Type), (Lean.Parsec String.Iterator α : Type)]

def HashMap := %first_succeeding [Std.HashMap, Lean.HashMap]
def HashSet := %first_succeeding [Std.HashSet, Lean.HashSet]

namespace HashMap

instance [BEq α] [Hashable α] : Membership α (HashMap α β) :=
  %first_succeeding [
    inferInstanceAs (Membership α (Std.HashMap α β)),
    ⟨fun k hm => hm.contains k⟩
  ]

instance [BEq α] [Hashable α] {x : α} {hm : HashMap α β} : Decidable (x ∈ hm) :=
  %first_succeeding [
    inferInstanceAs (Decidable (x ∈ (hm : Std.HashMap α β))),
    inferInstanceAs (Decidable (hm.contains x = true))
  ]

instance instGetElemHashMap [BEq α] [Hashable α] [Inhabited β] : GetElem (HashMap α β) α β (fun m a => a ∈ m) :=
  %first_succeeding [
    inferInstanceAs (GetElem (Std.HashMap α β) α β (fun m a => a ∈ m)),
    ⟨fun m a _ok => m.find! a⟩,
    ⟨fun m a _ok => m.find! a, fun m a => Lean.HashMap.find? m a, fun m a => Lean.HashMap.find! m a⟩
  ]

def get? {_ : BEq α} {_ : Hashable α} : HashMap α β → α → Option β :=
  %first_defined [Std.HashMap.get?, Lean.HashMap.find?]

def get! {_ : BEq α} {_ : Hashable α} [Inhabited β] : HashMap α β → α → β :=
  %first_defined [Std.HashMap.get!, Lean.HashMap.find!]

def getD {_ : BEq α} {_ : Hashable α} [Inhabited β] : HashMap α β → α → β → β :=
  %first_defined [Std.HashMap.getD, Lean.HashMap.findD]


%if_bound GetElem?
  instance [BEq α] [Hashable α] [Inhabited β] : GetElem? (HashMap α β) α β (fun m a => a ∈ m) :=
    %first_succeeding [
      inferInstanceAs (GetElem? (Std.HashMap α β) α β (fun m a => a ∈ m)),
      @GetElem?.mk _ _ _ _ instGetElemHashMap (fun m a => m.get? a) (fun m a => m.get! a)
    ]

instance [BEq α] [Hashable α] : EmptyCollection (HashMap α β) := ⟨%first_succeeding [Std.HashMap.empty, Lean.HashMap.empty]⟩
