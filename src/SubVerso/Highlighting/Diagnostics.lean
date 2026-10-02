/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Lean.Data.Json
public import Lean.Data.NameMap
public import SubVerso.Compat

public section

open Lean
open SubVerso.Compat

namespace SubVerso.Highlighting

/--
Metadata about highlighting, separate from messages produced by the highlighted code.

Design choice: return a summary alongside each highlighting result, rather than attach lookup
status to every token. Clients can render one warning per missing module, even when many tokens
refer to it. Combining results merges these summaries; individual occurrences are not retained.
The summary covers the whole result. Slicing its highlighted output does not narrow the summary;
clients that need a warning for a smaller excerpt should collect diagnostics for that excerpt.
-/
structure Diagnostics where
  /--
  Defining modules whose documentation metadata was unavailable when a docstring lookup failed.
  Kept as a set so clients retain the uniqueness invariant. JSON encodes it as a sorted array.

  These names suggest `import all M`; they do not prove that a docstring exists. With metadata
  unavailable, even an undocumented declaration can contribute its module. Inherited documentation
  contributes the module reached through the loaded `inherit_doc` references.
  -/
  missingDocStringModules : NameSet := {}
deriving Inhabited

instance : Repr Diagnostics where
  reprPrec d _ :=
    "{ missingDocStringModules := " ++ repr d.missingDocStringModules.toArray ++ " }"

/-- Construct diagnostic metadata from module names, discarding duplicates. -/
def Diagnostics.ofMissingDocStringModules (modules : Array Name) : Diagnostics :=
  { missingDocStringModules := modules.foldl (fun names name => names.insert name) ({} : NameSet) }

-- Compare the elements, independently of the tree representation used by the Lean version.
instance : BEq Diagnostics where
  beq a b := a.missingDocStringModules.toArray == b.missingDocStringModules.toArray

instance : ToJson Diagnostics where
  toJson d := Json.mkObj [("missingDocStringModules", toJson d.missingDocStringModules.toArray)]

instance : FromJson Diagnostics where
  fromJson? json :=
    Diagnostics.ofMissingDocStringModules <$> json.getObjValAs? (Array Name) "missingDocStringModules"

/--
Read the `diagnostics` field shared by helper results, modules, and examples. Missing or null
fields represent empty diagnostics, allowing payloads from older SubVerso versions to be decoded.
-/
def Diagnostics.fromJsonField? (json : Json) : Except String Diagnostics :=
  if json.getObjValD "diagnostics" == .null then pure {}
  else json.getObjValAs? Diagnostics "diagnostics"

open Syntax in
instance : Quote Diagnostics where
  quote d := mkCApp ``Diagnostics.ofMissingDocStringModules #[quote d.missingDocStringModules.toArray]

/-- Combine diagnostics from separately highlighted pieces of code. -/
def Diagnostics.append (a b : Diagnostics) : Diagnostics :=
  { missingDocStringModules := Compat.NameSet.union a.missingDocStringModules b.missingDocStringModules }

instance : Append Diagnostics := ⟨Diagnostics.append⟩
