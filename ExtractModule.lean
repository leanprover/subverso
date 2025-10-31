/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Compat
import SubVerso.Examples.Env
import SubVerso.Module

open Lean Elab Frontend
open Lean.Elab.Command hiding Context
open SubVerso Examples Module
open SubVerso.Highlighting (Highlighted highlight highlightMany)

def helpText : String :=
"Extract a module's highlighted representation as JSON

Usage: subverso-extract-mod [OPTS] MOD [OUT]

MOD is the name of a Lean module, and OUT is the destination of the JSON.
If OUT is not specified, the JSON is emitted to standard output.

OPTS may be:
  --suppress-namespace NS
    Suppress the showing of namespace NS in metadata

  --suppress-namespaces FILE
    Suppress the showing of the whitespace-delimited list of namespaces in FILE

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

/--
Extends the last token's trailing whitespace to include the rest of the file.
-/
partial def wholeFile (contents : String) (stx : Syntax) : Syntax :=
  wholeFile' stx |>.getD stx
where
  wholeFile' : Syntax → Option Syntax
  | Syntax.atom info val => pure <| Syntax.atom (wholeFileInfo info) val
  | Syntax.ident info rawVal val pre => pure <| Syntax.ident (wholeFileInfo info) rawVal val pre
  | Syntax.node info k args => do
    for i in [0:args.size - 1] do
      let j := args.size - (i + 1)
      if let some s := wholeFile' args[j]! then
        let args := args.set! j s
        return Syntax.node info k args
    none
  | .missing => none

  wholeFileInfo : SourceInfo → SourceInfo
    | .original l l' t _ => .original l l' t (Compat.String.endPos contents)
    | i => i


unsafe def go (suppressedNamespaces : Array Name) (mod : String) (out : IO.FS.Stream) : IO UInt32 := do
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

    let commandState : Command.State := { env, maxRecDepth := defaultMaxRecDepth, messages := msgs }
    let scopes :=
      let sc := commandState.scopes[0]!
      {sc with opts := sc.opts.setBool `pp.tagAppFns true } :: commandState.scopes.tail!
    let commandState := { commandState with scopes }
    let cmdPos := parserState.pos
    let cmdSt ← IO.mkRef { commandState, parserState, cmdPos }

    let res ← Compat.Frontend.processCommands headerStx pctx cmdSt

    let infos := (← cmdSt.get).commandState.infoState.trees
    let msgs := Array.flatten (res.items.map (Compat.messageLogArray ·.messages))

    let res := res.updateLeading contents

    let hls ← (Frontend.runCommandElabM <| liftTermElabM <| Highlighting.highlightFrontendResult res (suppressNamespaces := suppressedNamespaces.toList)) pctx cmdSt

    let items : Array ModuleItem := hls.zip res.syntax |>.map fun (hl, stx) => {
      defines := hl.definedNames.toArray,
      kind := stx.getKind,
      range := stx.getRange?.map fun ⟨s, e⟩ => (fm.toPosition s, fm.toPosition e),
      code := hl
    }

    out.putStrLn (toString (Module.mk items).toJson)

    return (0 : UInt32)

  catch e =>
    IO.eprintln s!"error finding highlighted code: {toString e}"
    return 2

structure Config where
  suppressedNamespaces : Array Name := #[]
  mod : String
  outFile : Option String := none

def Config.fromArgs (args : List String) : IO Config := go #[] args
where
  go (nss : Array Name) : List String → IO Config
    | "--suppress-namespace" :: more =>
      if let ns :: more := more then
        go (nss.push ns.toName) more
      else
        throw <| .userError "No namespace given after --suppress-namespace"
    | "--suppress-namespaces" :: more => do
      if let file :: more := more then
        let contents ← IO.FS.readFile file
        let nss' := Compat.String.splitToList contents (·.isWhitespace) |>.filter (!·.isEmpty) |>.map (·.toName)
        go (nss ++ nss') more
      else
        throw <| .userError "No namespace file given after --suppress-namespaces"
    | [mod] => pure {suppressedNamespaces := nss, mod}
    | [mod, outFile] => pure {suppressedNamespaces := nss, mod, outFile := some outFile}
    | other => throw <| .userError s!"Didn't understand remaining arguments: {other}"

unsafe def main (args : List String) : IO UInt32 := do
  try
    let {suppressedNamespaces, mod, outFile} ← Config.fromArgs args
    match outFile with
    | none =>
      go suppressedNamespaces mod (← IO.getStdout)
    | some outFile =>
      if let some p := (outFile : System.FilePath).parent then
        IO.FS.createDirAll p
      IO.FS.withFile outFile .write fun h =>
        go suppressedNamespaces mod (.ofHandle h)
  catch e =>
    IO.eprintln e
    IO.println helpText
    pure 1
