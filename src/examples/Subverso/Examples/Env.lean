import Lean
import Subverso.Highlighting

open Lean

namespace Subverso.Examples
open Subverso.Highlighting

instance : ToJson Position where
  toJson | ⟨l, c⟩ => toJson (l, c)

instance : FromJson Position where
  fromJson?
    | .arr #[l, c] => Position.mk <$> fromJson? l <*> fromJson? c
    | other => .error s!"Couldn't decode position from {other}"

example : fromJson? (toJson (⟨1, 5⟩ : Position)) = .ok (⟨1, 5⟩ : Position) := rfl

instance : ToJson MessageSeverity where
  toJson
    | .error => "error"
    | .warning => "warning"
    | .information => "information"

instance : FromJson MessageSeverity where
  fromJson?
    | "error" => .ok .error
    | "warning" => .ok .warning
    | "information" => .ok .information
    | other => .error s!"Expected 'error', 'warning', or 'information', got {other}"

theorem MessageSeverity.fromJson_toJson_ok (s : MessageSeverity) : fromJson? (toJson s) = .ok s := by
  cases s <;> simp [toJson, fromJson?]

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
