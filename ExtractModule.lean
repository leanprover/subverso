/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Compat
import SubVerso.Examples.Env
import SubVerso.Module
import Lean.Util.Paths

open Lean Elab Frontend
open Lean.Elab.Command hiding Context
open SubVerso Examples Module
open SubVerso.Highlighting (Highlighted highlight)

def helpText : String :=
"Extract a module's highlighted representation as JSON

Usage: subverso-extract-mod MOD [OUT]

MOD is the name of a Lean module, and OUT is the destination of the JSON.
If OUT is not specified, the JSON is emitted to standard output.

Each command in the module is represented as a JSON object with the following
fields:

 * \"kind\": the syntax kind of the command, as emitted by the Lean parser

 * \"range\": the start and end source positions of the command. Line and column
   numbers are one-based, so the start of the file is {\"line\": 1, \"column\": 1},
   and columns are in terms of Unicode code points.

 * \"defines\": the names defined in the command, as an array of strings.

 * \"code\": the JSON serialization of SubVerso's highlighted code datatype. The
   specifics of this representation are an implementation detail, and it should
   be deserialized using the same version of SubVerso.
"


unsafe def go (mod : String) (out : IO.FS.Stream) : IO UInt32 := do
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
    let contents ← IO.FS.readFile fname
    let fm := FileMap.ofString contents
    let ictx := Parser.mkInputContext contents fname.toString
    let (headerStx, parserState, msgs) ← Parser.parseHeader ictx
    let imports := headerToImports headerStx
    enableInitializersExecution
    let env ← Compat.importModules imports {}
    let pctx : Context := {inputCtx := ictx}

    let commandState := {env, maxRecDepth := defaultMaxRecDepth, messages := msgs}
    let cmdPos := parserState.pos
    let cmdSt ← IO.mkRef {commandState, parserState, cmdPos}

    processCommands pctx cmdSt

    let cmdStx := (← cmdSt.get).commands

    let infos := (← cmdSt.get).commandState.infoState.trees
    let msgs := Compat.messageLogArray (← cmdSt.get).commandState.messages

    let mut items : Array ModuleItem := #[]

    let .node _ _ cmds := mkNullNode (#[headerStx] ++ cmdStx) |>.updateLeading
      | panic! "updateLeading created non-node"

    for cmd in cmds do
      let hl ← (Frontend.runCommandElabM <| liftTermElabM <| highlight cmd msgs infos) pctx cmdSt
      let defs := hl.definedNames.toArray

      let range := cmd.getRange?.map fun ⟨s, e⟩ => (fm.toPosition s, fm.toPosition e)

      items := items.push {
        defines := defs,
        kind := cmd.getKind,
        range := range,
        code := hl
      }

    out.putStrLn (toString (Json.arr (items.map toJson)))

    return (0 : UInt32)

  catch e =>
    IO.eprintln s!"error finding highlighted code: {toString e}"
    return 2

unsafe def main : (args : List String) → IO UInt32
  | [mod] => do
    go mod (← IO.getStdout)
  | [mod, outFile] => do
    if let some p := (outFile : System.FilePath).parent then
      IO.FS.createDirAll p
    IO.FS.withFile outFile .write fun h =>
      go mod (.ofHandle h)
  | other => do
    IO.eprintln s!"Didn't understand args: {other}"
    IO.println helpText
    pure 1
