/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import SubVerso.Compat
public import Lean.DocString
-- Access to inheritance is kept here until Lean provides a richer lookup API.
-- nomodule skip
import all Lean.DocString.Extension
import Lean.DeclarationRange

public section

open Lean SubVerso.Compat

namespace SubVerso

/--
The outcome of a documentation lookup. This API is staged in SubVerso for use by Verso before
upstreaming to Lean; its shape may change as those consumers gain experience with it.
-/
inductive DocStringLookup (α : Type) where
  /-- Documentation was found. -/
  | found (doc : α)
  /-- No documentation was found, with no known unavailable metadata blocking the lookup. -/
  | absent
  /--
  Documentation metadata from this module is unavailable. Whether documentation exists is unknown;
  a batch build can load the metadata with `import all`.
  -/
  | unavailable (moduleName : Name)
deriving Repr, BEq

instance : Inhabited (DocStringLookup α) := ⟨.absent⟩

/-- Forget why documentation was not found, recovering the usual optional lookup result. -/
def DocStringLookup.toOption : DocStringLookup α → Option α
  | .found doc => some doc
  | .absent | .unavailable _ => none

-- Lean's inheritance extension is private. Keep this dependency isolated and use the existing
-- lookup behavior on older Lean versions, where the module-system distinction is unnecessary.
private def inheritedDocString? (env : Environment) (declName : Name) : Option Name :=
  %first_succeeding [
    Lean.inheritDocStringExt.find? (level := .server) env declName,
    none
  ]

private partial def unavailableDocStringModule? (env : Environment) (declName : Name) : Option Name :=
  if let some target := inheritedDocString? env declName then
    unavailableDocStringModule? env target
  else
    %first_succeeding [
      do
        let idx ← env.getModuleIdxFor? declName
        let mod ← env.header.modules[idx.toNat]?
        let data ← env.header.moduleData[idx.toNat]?
        if !data.isModule || mod.importAll then none
        -- Declaration ranges and docstrings share server data. Check the whole module so names
        -- without their own range (e.g. generated declarations) also benefit from this evidence.
        -- Upstream follow-up: expose whether server metadata is available for a module in an
        -- environment. Until then, a module with no ranges may be reported as unavailable even
        -- when its metadata was loaded.
        else if !(declRangeExt.getModuleEntries (level := .server) env idx).isEmpty then none
        else some mod.module,
      none
    ]

/--
Look up a rendered docstring, distinguishing an absent docstring from unavailable import metadata.

Successful lookups use `Lean.findDocString?`, including its tactic aliases, inherited documentation,
builtins, and rendering options. Failed lookups follow any loaded `inherit_doc` references before
checking the defining module's effective import mode, including transitive imports.

`.unavailable M` suggests `import all M`; it does not establish that documentation exists. No
additional metadata is loaded by this function. Server metadata availability currently uses
declaration ranges as evidence, pending an authoritative Lean environment API. On older Lean
versions without the module system, results are always `.found` or `.absent`; rendering options
not supported by that Lean version are ignored.
-/
def findDocString (env : Environment) (declName : Name) (includeBuiltin := true)
    (options : Options := {}) (currNamespace : Name := .anonymous) (openDecls : List OpenDecl := []) :
    IO (DocStringLookup String) := do
  let docs ← %first_succeeding [
    Lean.findDocString? env declName includeBuiltin options currNamespace openDecls,
    Lean.findDocString? env declName includeBuiltin
  ]
  if let some doc := docs then return .found doc
  let declName := %first_succeeding [
    Lean.Parser.Tactic.Doc.alternativeOfTactic env declName |>.getD declName,
    declName
  ]
  if let some mod := unavailableDocStringModule? env declName then
    return .unavailable mod
  return .absent
