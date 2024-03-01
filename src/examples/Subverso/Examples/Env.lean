import Lean
import Subverso.Highlighting

open Lean

namespace Subverso.Examples
open Subverso.Highlighting

deriving instance ToJson, FromJson for Position, MessageSeverity

structure Example where
  highlighted : Array Highlighted
  messages : List (MessageSeverity × String)
  original : String
  start : Lean.Position
  stop : Lean.Position
deriving ToJson, FromJson

initialize highlighted : PersistentEnvExtension (NameMap Json) (Name × Example) (NameMap Json) ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := fun imported => do
      let mut s := {}
      for imp in imported do
        for found in imp do
          s := s.mergeBy (fun _ _ json => json) found
      pure s
    addEntryFn := fun s (n, val) => s.insert n (toJson val)
    exportEntriesFn := fun s => #[s]
  }
