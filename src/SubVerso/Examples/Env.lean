/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Highlighting

open Lean

namespace SubVerso.Examples
open SubVerso.Highlighting

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

deriving instance Repr for MessageSeverity

structure Example where
  highlighted : Array Highlighted
  messages : List (MessageSeverity × String)
  original : String
  start : Lean.Position
  stop : Lean.Position
  /--
  Does the example follow some particular hierarchical structure?

  Libraries that build on top of SubVerso are encouraged to distinguish examples that encode a
  special structure by setting their kind. For instance, an example that includes a term and its
  type as named sub-terms might have the kind `` `typedTerm ``. The code that loads and renders such
  examples can then check for the kind, and throw a user-friendly error if it's the wrong kind.
  -/
  kind : Option Name := none
deriving ToJson, FromJson, Repr

register_option SubVerso.examples.suppressedNamespaces : String := {
  defValue := "",
  group := "SubVerso",
  descr := "A space-separated list of namespaces to suppress in highlighted example code"
}

def getSuppressed [Monad m] [MonadOptions m] : m (List Name) := do
  return (← getOptions) |> SubVerso.examples.suppressedNamespaces.get |>.splitOn " " |>.map (·.toName)



initialize highlighted : PersistentEnvExtension (NameMap (NameMap Json)) (Name × Name × Example) (NameMap (NameMap Json)) ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := fun imported => do
      let mut s := {}
      for imp in imported do
        for found in imp do
          s := s.mergeBy (fun _ exs1 exs2 => exs1.mergeBy (fun _ _ v => v) exs2) found
      pure s
    addEntryFn := fun s (mod, ex, val) =>
      let forMod := s.find? mod |>.getD .empty
      s.insert mod (forMod.insert ex (toJson val))
    exportEntriesFn := fun s => #[s]
  }
