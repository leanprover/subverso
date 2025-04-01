/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Elab
import Lean.Util.Paths

open Lean Elab Term

-- This was introduced in #3159, so we need a shim:
open Lean Elab Command in
#eval show CommandElabM Unit from do
  if !(← getEnv).contains `Lean.Elab.PartialContextInfo then
    dbg_trace "lkj"
    let cmd ← `(def $(mkIdent `Lean.Elab.ContextInfo.mergeIntoOuter?) (inner: ContextInfo) (_outer : Option ContextInfo) : ContextInfo := inner)
    elabCommand cmd

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
  let msgs ← Core.getMessageLog
  for e in es.getElems do
    Core.setMessageLog msgs
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

scoped syntax "export_from_namespaces " "(" ident+ ") " "(" ident+ ")" : command

elab_rules : command
  | `(export_from_namespaces ($nss*) ($xs*)) => do
    let env ← getEnv
    let mut toAlias := #[]
    for x in xs do
      let x' := x.getId
      let mut found := none
      for ns in nss do
        let ns' := ns.getId
        let y := ns' ++ x'
        if env.contains y then
          found := some (ns, x)
          break
      if let some ok := found then
        toAlias := toAlias.push ok
      else
        throwErrorAt x "'{x}' not found in namespaces {indentD <| toMessageData nss}"
    for (ns, x) in toAlias do
      Command.elabCommand <| ← `(export $ns ($x))

open Command in
elab "%if_bound" x:ident cmd:command : command => do
  if (← getEnv).contains x.getId then elabCommand cmd

def importModules (imports : Array Import) (opts : Options) (trustLevel : UInt32 := 0) : IO Environment :=
  Lean.importModules (%first_succeeding [imports, imports.toList]) opts (trustLevel := trustLevel)

def mkRefIdentFVar [Monad m] [MonadEnv m] (id : FVarId) : m Lean.Lsp.RefIdent := do
  pure %first_succeeding [
    .fvar (← getEnv).mainModule.toString id.name.toString,
    .fvar (← getEnv).mainModule id,
    .fvar id
  ]

def refIdentCase (ri : Lsp.RefIdent)
    (onFVar : FVarId → α)
    (onConst : Name → α) : α :=
  %first_succeeding [
    match ri with
    | .fvar _ id => onFVar ⟨id.toName⟩
    | .const _ x => onConst x.toName,
    match ri with
    | .fvar _ id => onFVar id
    | .const _ x => onConst x,
    match ri with
    | .fvar id => onFVar id
    | .const x => onConst x
  ]

/--
If the provided syntax is the syntax of the `rw` or `rewrite` tactics, returns the syntax of the
closing bracket of the rewrite rules. Otherwise returns `none`.

This is needed because the syntax of `rw` changed in 4.14, so it's no longer possible to have a
quasiquote that matches both versions.
-/
def rwTacticRightBracket? (stx : Syntax) : Option Syntax := Id.run do
  if let .node _ k children := stx then
    if k ∈ [``Lean.Parser.Tactic.rwSeq, ``Lean.Parser.Tactic.rewriteSeq] then
      for child in children do
        match child with
        | `(Lean.Parser.Tactic.rwRuleSeq|[$_rs,*]%$brak) => return some brak
        | _ => continue
  return none


def getDeclarationRange? [Monad m] [MonadFileMap m] (stx : Syntax) : m (Option DeclarationRange) :=
  %first_succeeding [Lean.Elab.getDeclarationRange? stx, some <$> Lean.Elab.getDeclarationRange stx]

def messageLogArray (msgs : Lean.MessageLog) : Array Lean.Message := %first_succeeding [msgs.toArray, msgs.msgs.toArray]

def initSrcSearchPath (pkgSearchPath : SearchPath := ∅) : IO SearchPath := do
  %first_succeeding [
    Lean.initSrcSearchPath (pkgSearchPath := pkgSearchPath),
    Lean.initSrcSearchPath (sp := pkgSearchPath),
    -- leanSysRoot seems to never have been used by this function
    Lean.initSrcSearchPath (leanSysroot := "") (sp := pkgSearchPath),
    Lean.initSrcSearchPath (_leanSysroot := "") (sp := pkgSearchPath)
  ]

namespace NameSet
def union (xs ys : NameSet) : NameSet :=
  xs.mergeBy (fun _ _ _ => .unit) ys
end NameSet

namespace List
-- bind was renamed to flatMap in 4.14
def flatMap (xs : List α) (f : α → List β) : List β :=
  %first_succeeding [_root_.List.flatMap xs f, _root_.List.bind xs f, _root_.List.flatMap f xs]
end List

namespace Array
-- back was renamed to back! in 4.14
def back! [Inhabited α] (xs : Array α) : α :=
  %first_succeeding [_root_.Array.back! xs, _root_.Array.back xs]
end Array

abbrev Parsec (α : Type) : Type :=
  %first_succeeding [
    (Lean.Parsec α : Type),
    (Lean.Parsec String.Iterator α : Type),
    (Std.Internal.Parsec String.Iterator α : Type)
  ]

namespace Parsec
export_from_namespaces
  (Lean.Parsec.String Lean.Parsec Std.Internal.Parsec.String Std.Internal.Parsec)
  (ws skipString skipChar many1Chars satisfy)
end Parsec

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

instance [BEq α] [Hashable α] : EmptyCollection (HashMap α β) :=
  ⟨%first_succeeding [Std.HashMap.emptyWithCapacity, Std.HashMap.empty, Lean.HashMap.empty]⟩

end HashMap

-- In nightly-2025-02-13, simp_arith became an error. Falling back to the old version is complicated
-- because there's no fully-backwards-compatible syntax to use here that works all the way back to Lean 4.0.0.
open Lean Elab Command in
#eval show CommandElabM Unit from do
  match Parser.runParserCategory (← getEnv) `tactic "simp +arith [*]" with
  | .ok stx =>
    let cmd ← `(command|macro "compat_simp_arith_all":tactic => `(tactic|$(⟨stx⟩)))
    elabCommand cmd
  | .error _ =>
    let cmd ← `(macro "compat_simp_arith_all":tactic => `(tactic| first | simp_arith [*] | simp (config := {arith := true}) [*]))
    elabCommand cmd

-- Elab.async got turned on in nightly-2025-03-16, but that means that the info tree is not always
-- ready when elaboration returns from an example. Thus, we need to turn it off for examples,
-- because otherwise proof states are not present when the highlighted code is generated.
open Lean Elab Command in
def commandWithoutAsync : (act : CommandElabM α) → CommandElabM α :=
  withScope fun sc =>
    {sc with opts := sc.opts.setBool `Elab.async false}

-- When a name is removed, hiding it is an error. This makes it tough to be compatible - we want to
-- hide Lean.HashMap in versions prior to nightly-2025-03-21, but cannot do so later.

/--
Opens the namespace, hiding those of the identifiers that actually exist.
-/
syntax "open" ident  "hiding" &"perhaps" "(" ident* ")" : command

open Lean Elab Command in
elab_rules : command
  | `(open $ns hiding perhaps ( $xs* )) => do
    let env ← getEnv
    let xs ← xs.filterM fun x => do
      let x := x.getId
      let nss ← resolveNamespace ns
      let names := nss.filter fun ns => env.contains (ns ++ x)
      return !names.isEmpty

    if xs.isEmpty then
      elabCommand (← `(open $ns:ident))
    else
      elabCommand (← `(open $ns:ident hiding $xs*))
