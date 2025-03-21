/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Compat
import SubVerso.Examples.Env
import Lean.Util.Paths

open Lean Elab Frontend
open Lean.Elab.Command (liftTermElabM)
open SubVerso Examples
open SubVerso.Highlighting (Highlighted highlight)

unsafe def main : (args : List String) → IO UInt32
  | [mod, outFile] => do
    try
      initSearchPath (← findSysroot)
      let modName := mod.toName

      let sp ← Compat.initSrcSearchPath
      let sp : SearchPath := (sp : List System.FilePath) ++ [("." : System.FilePath)]
      let fname ← do
        if let some fname ← sp.findModuleWithExt "lean" modName then
          pure fname
        else
          throw <| IO.userError s!"Failed to load {modName} from {sp}"
      let ictx := Parser.mkInputContext (← IO.FS.readFile fname) fname.toString
      let (headerStx, parserState, msgs) ← Parser.parseHeader ictx
      let imports := headerToImports headerStx
      enableInitializersExecution
      let env ← importModules imports {}
      let pctx : Context := {inputCtx := ictx}

      let commandState := {env, maxRecDepth := defaultMaxRecDepth, messages := msgs}
      let cmdPos := parserState.pos
      let cmdSt ← IO.mkRef {commandState, parserState, cmdPos}
      processCommands pctx cmdSt

      let cmdStx := (← cmdSt.get).commands
      let infos := (← cmdSt.get).commandState.infoState.trees
      let msgs := Compat.messageLogArray (← cmdSt.get).commandState.messages

      let mut hls := Highlighted.empty
      for cmd in #[headerStx] ++ cmdStx do
        hls := hls ++ (← (Frontend.runCommandElabM <| liftTermElabM <| highlight cmd msgs infos) pctx cmdSt)
      if let some p := (outFile : System.FilePath).parent then
        IO.FS.createDirAll p
      IO.FS.writeFile outFile (toString (ToJson.toJson hls) ++ "\n")
      return (0 : UInt32)

    catch e =>
      IO.eprintln s!"error finding highlighted code: {toString e}"
      return 2
  | other => do
    IO.eprintln s!"Didn't understand args: {other}"
    pure 1
