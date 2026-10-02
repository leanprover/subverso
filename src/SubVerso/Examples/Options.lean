/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import SubVerso.Compat
public import Lean.Data.Options
public import Lean.Data.Name
public section

/-!
Options that control how SubVerso highlights code.
-/

open Lean

register_option SubVerso.examples.suppressedNamespaces : String :=
  SubVerso.Compat.Option.Decl.mk
    (defValue := "")
    (group := "SubVerso")
    (descr := "A space-separated list of namespaces to suppress in highlighted example code")

namespace SubVerso.Examples

/-- The namespaces listed in the `SubVerso.examples.suppressedNamespaces` option. -/
def getSuppressed [Monad m] [MonadOptions m] : m (List Name) := do
  return (← getOptions) |> SubVerso.examples.suppressedNamespaces.get |>.splitOn " " |>.map (·.toName)

end SubVerso.Examples
