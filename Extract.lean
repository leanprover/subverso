/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Compat
import SubVerso.Examples.Env

open Lean
open SubVerso.Examples

unsafe def main : (args : List String) → IO UInt32
  | [mod, outFile] => do
    try
      initSearchPath (← findSysroot)
      let modName := mod.toName
      enableInitializersExecution
      let env ← SubVerso.Compat.importModules #[SubVerso.Compat.mkImport modName] {}
      let modExamples := highlighted.getState env
      let useful := relevant modName modExamples
      let exJson := Json.mkObj useful
      IO.println s!"Processed {useful.length} examples for module '{modName}'"
      if let some p := (outFile : System.FilePath).parent then
        IO.FS.createDirAll p
      IO.FS.writeFile outFile (toString exJson ++ "\n")
      return 0
    catch e =>
      IO.eprintln s!"error finding highlighted code: {toString e}"
      return 2
  | other => do
    IO.eprintln s!"Didn't understand args: {other}"
    pure 1
where
  relevant (mod : Name) (examples : NameMap (NameMap Json)) : List (String × Json) :=
    examples.find? mod |>.getD {} |>.toList |>.map fun (name, ex) =>
      (name.toString, ex)
