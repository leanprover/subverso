/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Elab
import Lean.Util.Paths

open Lean Elab Term

section
open Lean Elab Command

-- This was introduced in #3159, so we need a shim:
#eval show CommandElabM Unit from do
  if !(← getEnv).contains `Lean.Elab.PartialContextInfo then
    let cmd ← `(def $(mkIdent `Lean.Elab.ContextInfo.mergeIntoOuter?) (inner: ContextInfo) (_outer : Option ContextInfo) : ContextInfo := inner)
    elabCommand cmd

#eval show CommandElabM Unit from do
  if !(← getEnv).contains `ByteArray.usize then
    let cmd ← `(def $(mkIdent `ByteArray.usize) (arr : ByteArray) : USize := arr.size.toUSize)
    elabCommand cmd

#eval show CommandElabM Unit from do
  if !(← getEnv).contains `Lean.MessageLog.toArray then
    let cmd ← `(def $(mkIdent `Lean.MessageLog.toArray) (msgs : Lean.MessageLog) : Array Lean.Message := msgs.toList.toArray)
    elabCommand cmd

-- This was introduced in Lean 4.3.0. Older versions need the definition.
#eval show CommandElabM Unit from do
  if !(← getEnv).contains `Lean.KVMap.erase then
    let cmd ←
      `(def $(mkIdent `Lean.KVMap.erase) : KVMap → Name → KVMap
          | ⟨m⟩, k => ⟨m.filter fun a => a.1 ≠ k⟩)
    elabCommand cmd

#eval show CommandElabM Unit from do
  if !(← getEnv).contains `String.Iterator.curr' then
    let cmd ←
      `(def $(mkIdent `String.Iterator.curr') (iter : String.Iterator) (_ : iter.hasNext) : Char := iter.curr)
    elabCommand cmd

#eval show CommandElabM Unit from do
  if !(← getEnv).contains `String.Iterator.next' then
    let cmd ←
      `(def $(mkIdent `String.Iterator.next') (iter : String.Iterator) (_ : iter.hasNext) : String.Iterator := iter.next)
    elabCommand cmd

#eval show CommandElabM Unit from do
  if !(← getEnv).contains `List.min? then
    let cmd ←
      `(def $(mkIdent `List.min?).{u} {α : Type u} [Min α] (xs : List α) : Option α := xs.foldl (fun x y => some (min (x.getD y) y)) none)
    elabCommand cmd

#eval show CommandElabM Unit from do
  if !(← getEnv).contains `String.stripPrefix then
    let cmd ←
      `(def $(mkIdent `String.stripPrefix) (s p : String) : String := if s.startsWith p then s.drop p.length else s)
    elabCommand cmd

#eval show CommandElabM Unit from do
  if !(← getEnv).contains `Substring.dropPrefix? then
    let cmd ←
      `(partial def $(mkIdent `Substring.dropPrefix?) (s p : Substring) : Option Substring := loop s.startPos p.startPos
        where
          loop p1 p2 :=
            if p2 < p.stopPos then
              if p1 < s.stopPos then
                loop (s.str.next p1) (p.str.next p2)
              else none
            else pure {s with startPos := p1}
        )
    elabCommand cmd

#eval show CommandElabM Unit from do
  if !(← getEnv).contains `String.dropPrefix? then
    let cmd ←
      `(partial def $(mkIdent `String.dropPrefix?) (s p : String) : Option Substring :=
          s.toSubstring.dropPrefix? p.toSubstring)
    elabCommand cmd

end

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

class CanBeArrayOrList (f : Type u → Type v) where
  asArray {α} : f α → Array α
  asList {α} : f α → List α

instance : CanBeArrayOrList Array where
  asArray := id
  asList := Array.toList

instance : CanBeArrayOrList List where
  asArray := List.toArray
  asList := id

def mkImport (module : Name) : Import :=
  %first_succeeding [
    {module}, {module, runtimeOnly := false}
  ]

open CanBeArrayOrList in
def importModules [CanBeArrayOrList f] (imports : f Import) (opts : Options) (trustLevel : UInt32 := 0) : IO Environment :=
  %first_succeeding [
    Lean.importModules (%first_succeeding [asArray imports, asList imports]) opts (trustLevel := trustLevel) (loadExts := true),
    Lean.importModules (%first_succeeding [asArray imports, asList imports]) opts (trustLevel := trustLevel)
  ]

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

section
/- Backports of syntax position functions from later Lean versions-/

def getInfoTrailing? (info : SourceInfo) : Option Substring :=
  match info with
  | .original (trailing := trailing) .. => some trailing
  | _ => none

def getInfoLeading? (info : SourceInfo) : Option Substring :=
  match info with
  | .original (leading := leading) .. => some leading
  | _ => none

/--
Gets the end position information from a `SourceInfo`, if available.
If `canonicalOnly` is true, then `.synthetic` syntax with `canonical := false`
will also return `none`.
-/
def getInfoTailPos? (info : SourceInfo) (canonicalOnly := false) : Option String.Pos :=
  match info, canonicalOnly with
  | .original (endPos := endPos) ..,  _
  | .synthetic (endPos := endPos) (canonical := true) .., _
  | .synthetic (endPos := endPos) .., false => some endPos
  | _, _     => none

/--
Gets the start position information from a `SourceInfo`, if available.
If `canonicalOnly` is true, then `.synthetic` syntax with `canonical := false`
will also return `none`.
-/
def getInfoHeadPos? (info : SourceInfo) (canonicalOnly := false) : Option String.Pos :=
  match info, canonicalOnly with
  | .original (pos := pos) ..,  _
  | .synthetic (pos := pos) (canonical := true) .., _
  | .synthetic (pos := pos) .., false => some pos
  | _, _     => none

/--
Gets the end position information of the trailing whitespace of a `SourceInfo`, if available.
If `canonicalOnly` is true, then `.synthetic` syntax with `canonical := false`
will also return `none`.
-/
def getInfoTrailingTailPos? (info : SourceInfo) (canonicalOnly := false) : Option String.Pos :=
  match getInfoTrailing? info with
  | some trailing => some trailing.stopPos
  | none => getInfoTailPos? info canonicalOnly

/--
Gets the start position information of the leading whitespace of a `SourceInfo`, if available.
If `canonicalOnly` is true, then `.synthetic` syntax with `canonical := false`
will also return `none`.
-/
def getInfoLeadingHeadPos? (info : SourceInfo) (canonicalOnly := false) : Option String.Pos :=
  match getInfoLeading? info with
  | some leading => some leading.startPos
  | none => getInfoHeadPos? info canonicalOnly

def getTrailingTailPos? (stx : Syntax) (canonicalOnly := false) : Option String.Pos :=
  getInfoTrailingTailPos? stx.getTailInfo canonicalOnly

def getLeadingHeadPos? (stx : Syntax) (canonicalOnly := false) : Option String.Pos :=
  getInfoLeadingHeadPos? stx.getHeadInfo canonicalOnly

end

/--
Decodes a byte array to a string.

Invalid encodings may panic or produce an unspecified result, depending on the Lean version in use.
-/
def decodeUTF8 (arr : ByteArray) : String :=
  %first_succeeding [
    String.fromUTF8! arr,
    String.fromUTF8Unchecked arr
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

def mapMessages (msgLog : Lean.MessageLog) (f : Lean.Message → Lean.Message) : Lean.MessageLog :=
  %first_succeeding [
    { msgLog with msgs := msgLog.msgs.map f },
    { msgLog with unreported := msgLog.unreported.map f }
  ]

set_option linter.unusedVariables false in
def initSrcSearchPath (pkgSearchPath : SearchPath := ∅) : IO SearchPath := do
  %first_succeeding [
    Lean.initSrcSearchPath (pkgSearchPath := pkgSearchPath),
    Lean.initSrcSearchPath (sp := pkgSearchPath),
    -- leanSysRoot seems to never have been used by this function
    Lean.initSrcSearchPath (leanSysroot := "") (sp := pkgSearchPath),
    Lean.initSrcSearchPath (_leanSysroot := "") (sp := pkgSearchPath),
    Lean.getSrcSearchPath
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

def insert {_ : BEq α} {_ : Hashable α} : HashMap α β → α → β → HashMap α β :=
  %first_defined [Std.HashMap.insert, Lean.HashMap.insert]

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

instance [BEq α] [Hashable α] : Inhabited (HashMap α β) := ⟨{}⟩

def map {_ : BEq α} {_ : Hashable α} (f : α → β → β) (xs : HashMap α β) : HashMap α β :=
  %first_succeeding [
    Std.HashMap.map f xs,
    Lean.HashMap.fold (fun r k v => r.insert k (f k v)) .empty xs
  ]

def keys {_ : BEq α} {_ : Hashable α} (xs : HashMap α β) : List α:=
  %first_succeeding [
    Std.HashMap.keys xs,
    Lean.HashMap.fold (fun r k _ => k :: r) [] xs
  ]


end HashMap

namespace HashSet

instance [BEq α] [Hashable α] : EmptyCollection (HashSet α) :=
  ⟨%first_succeeding [Std.HashSet.emptyWithCapacity, Std.HashSet.empty, Lean.HashSet.empty]⟩

end HashSet

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
def commandWithoutAsync (act : CommandElabM α) : CommandElabM α := do
  -- withScope doesn't work here, because it restores other changes made to the scopes by the
  -- commands (e.g. variables, `open`, etc)
  match (← get).scopes with
  | [] => act
  | h :: t =>
    let mut orig : Option Bool := none
    try
      orig := h.opts.get? `Elab.async
      modify fun s => { s with scopes := { h with opts := h.opts.setBool `Elab.async false } :: t }
      act
    finally
      -- It's important to just narrowly undo the option change here, and otherwise leave the scope alone
      if let h :: t := (← get).scopes then
        let opts := orig.map (h.opts.setBool `Elab.async) |>.getD (h.opts.erase `Elab.async)
        modify fun s => { s with scopes := { h with opts := opts } :: t }

def registerEnvExtension (mkInitial : IO σ) :=
  %first_succeeding [Lean.registerEnvExtension mkInitial (asyncMode := .sync), Lean.registerEnvExtension mkInitial]

def registerPersistentEnvExtension {α β σ : Type} [Inhabited σ] (descr : PersistentEnvExtensionDescr α β σ) :=
  %first_succeeding [
    Lean.registerPersistentEnvExtension {descr with asyncMode := .sync},
    Lean.registerPersistentEnvExtension descr
  ]

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
