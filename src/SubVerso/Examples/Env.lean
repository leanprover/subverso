/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import SubVerso.Highlighting
public import Lean.Data.Options
public import Lean.Data.Json
public import Lean.Data.Position
public import Lean.Message
public section

open Lean

register_option SubVerso.examples.suppressedNamespaces : String := {
  defValue := "",
  group := "SubVerso",
  descr := "A space-separated list of namespaces to suppress in highlighted example code"
}

namespace SubVerso.Examples
open SubVerso.Highlighting

instance : ToJson Position where
  toJson | ⟨l, c⟩ => toJson (l, c)

instance : FromJson Position where
  fromJson?
    | .arr #[l, c] => Position.mk <$> fromJson? l <*> fromJson? c
    | other => .error s!"Couldn't decode position from {other}"


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

open Syntax in
instance : Quote Lean.Position where
  quote s :=
    mkCApp ``Lean.Position.mk #[quote s.line, quote s.column]

open Syntax in
instance : Quote MessageSeverity where
  quote s :=
    let n :=
      match s with
      | .error => ``MessageSeverity.error
      | .information => ``MessageSeverity.information
      | .warning => ``MessageSeverity.warning
    mkCApp n #[]

instance : Quote Example where
  quote
    | ⟨highlighted, messages, original, start, stop, kind⟩ =>
      Syntax.mkCApp ``Example.mk #[
        quote highlighted,
        quote messages,
        quote original,
        quote start,
        quote stop,
        quote kind
      ]

initialize highlighted : PersistentEnvExtension (NameMap (NameMap Json)) (Name × Name × Example) (NameMap (NameMap Json)) ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := fun imported => do
      let mut s := {}
      for imp in imported do
        for found in imp do
          s := Compat.NameMap.mergeBy (fun _ exs1 exs2 => Compat.NameMap.mergeBy (fun _ _ v => v) exs1 exs2) s found
      pure s
    addEntryFn := fun s (mod, ex, val) =>
      let forMod := s.find? mod |>.getD .empty
      s.insert mod (forMod.insert ex (toJson val))
    exportEntriesFn := fun s => #[s]
  }
