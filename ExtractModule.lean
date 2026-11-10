/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Compat
import SubVerso.Module

open Lean Elab Frontend
open Lean.Elab.Command hiding Context
open SubVerso Module
open SubVerso.Highlighting (Highlighted highlight highlightMany highlightFrontendResult Timings)
open SubVerso.Highlighting.Timings (Category Counter startCategories stopCategories seconds)

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

  --not-server
    When elaborating a module, import only the public parts. This emulates the
    behavior of the command-line compiler instead of the language server.

  --setup FILE
    Load imported modules from the artifacts listed in FILE, which should be a in
    Lake's module setup JSON format. Imports that FILE doesn't list are found
    through LEAN_PATH. Toolchains without Lake module setups ignore this option.

  --timings
    After the run, write one line of JSON to standard error with the wall-clock
    and CPU seconds of each phase (import, elaboration, highlighting, export,
    writing), the seconds spent on each category of highlighting work (exempting
    calls to nested highlighting), and counts of pretty-printer and MetaM calls.
    CPU seconds are null on toolchains that can't report them.

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

/-- Returns the node kind of the command, skipping outer `in` nodes. -/
partial def commandKind (cmd : Syntax) : SyntaxNodeKind :=
  match cmd with
  | `(command|$_cmd1 in $cmd2) => commandKind cmd2
  | _ => cmd.getKind

structure Timer where
  phases : IO.Ref (Array (String × Nat × Option Nat))
  highlighting : IO.Ref Timings

def Timer.new : IO Timer := do
  pure { phases := ← IO.mkRef #[], highlighting := ← IO.mkRef {} }

def phase (timer? : Option Timer) (name : String) (act : IO α) (categories : Bool := false) : IO α := do
  match timer? with
  | none => act
  | some timer =>
    let cpu0 ← Compat.cpuMillis?
    let t0 ← IO.monoNanosNow
    if categories then startCategories timer.highlighting t0
    let r ← act
    let t1 ← IO.monoNanosNow
    if categories then stopCategories timer.highlighting t1
    let cpu1 ← Compat.cpuMillis?
    timer.phases.modify (·.push (name, t1 - t0, (· - ·) <$> cpu1 <*> cpu0))
    pure r

def timesJson (wallNanos : Nat) (cpuMillis? : Option Nat) : Json :=
  Json.mkObj [
    ("wallSeconds", seconds wallNanos),
    ("cpuSeconds", cpuMillis?.map (fun ms => Json.num ⟨Int.ofNat ms, 3⟩) |>.getD Json.null)
  ]

def Timer.report (timer : Timer) (wallNanos : Nat) : IO Json := do
  let phases ← timer.phases.get
  let hl ← timer.highlighting.get
  let cpu? ← Compat.cpuMillis?
  pure <| Json.mkObj [
    ("phases", Json.mkObj <| phases.toList.map fun (name, wall, cpu?) => (name, timesJson wall cpu?)),
    ("total", timesJson wallNanos cpu?),
    ("highlighting", Json.mkObj <| Category.all.toList.map fun c =>
      (c.name, seconds (hl.exclusive[c.index]?.getD 0))),
    ("counters", Json.mkObj <| Counter.all.toList.map fun c =>
      (c.name, ((hl.counters[c.index]?.getD 0 : Nat) : Json)))
  ]

unsafe def go (timer? : Option Timer) (asServer : Bool) (suppressedNamespaces : Array Name) (setupFile? : Option System.FilePath) (mod : String) (out : IO.FS.Stream) : IO UInt32 := do
  try
    let (contents, fm, ictx, headerStx, parserState, msgs, env) ← phase timer? "import" do
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
      let isModule := Compat.isModule headerStx
      let setupJson? ← setupFile?.mapM IO.FS.readFile
      let env ← Compat.importModules imports {} (isModule := isModule) (asServer := asServer) (setupJson? := setupJson?)
      pure (contents, fm, ictx, headerStx, parserState, msgs, env)
    let pctx : Context := {inputCtx := ictx}

    let commandState : Command.State := { env, maxRecDepth := defaultMaxRecDepth, messages := msgs }
    let scopes :=
      let sc := commandState.scopes[0]!
      {sc with opts := sc.opts.setBool `pp.tagAppFns true } :: commandState.scopes.tail!
    let commandState := { commandState with scopes }
    let cmdPos := parserState.pos
    let cmdSt ← IO.mkRef { commandState, parserState, cmdPos }

    let res ← phase timer? "elaboration" do
      Compat.Frontend.processCommands headerStx pctx cmdSt

    let (res, hls) ← phase timer? "highlighting" (categories := true) do
      let res ← IO.lazyPure fun _ => res.updateLeading contents
      let hls ← (Frontend.runCommandElabM <| liftTermElabM <|
        highlightFrontendResult res (suppressNamespaces := suppressedNamespaces.toList)
          (timings? := timer?.map (·.highlighting))) pctx cmdSt
      pure (res, hls)

    let json ← phase timer? "export" do
      IO.lazyPure fun _ =>
        let items : Array ModuleItem := hls.zip res.syntax |>.map fun (hl, stx) => {
          defines := hl.definedNames.toArray,
          kind := commandKind stx,
          range := stx.getRange?.map fun ⟨s, e⟩ => (fm.toPosition s, fm.toPosition e),
          code := hl
        }
        toString (Module.mk items).toJson

    phase timer? "writing" do
      out.putStrLn json
      out.flush

    return (0 : UInt32)

  catch e =>
    IO.eprintln s!"error finding highlighted code: {toString e}"
    return 2

structure Config where
  asServer : Bool
  suppressedNamespaces : Array Name := #[]
  setupFile? : Option System.FilePath := none
  mod : String
  outFile : Option String := none
  timings : Bool := false

def Config.fromArgs (args : List String) : IO Config := go true #[] none false args
where
  go (asServer : Bool) (nss : Array Name) (setupFile? : Option System.FilePath) (timings : Bool) : List String → IO Config
    | "--suppress-namespace" :: more =>
      if let ns :: more := more then
        go asServer (nss.push ns.toName) setupFile? timings more
      else
        throw <| .userError "No namespace given after --suppress-namespace"
    | "--suppress-namespaces" :: more => do
      if let file :: more := more then
        let contents ← IO.FS.readFile file
        let nss' := Compat.String.splitToList contents (·.isWhitespace) |>.filter (!·.isEmpty) |>.map (·.toName)
        go asServer (nss ++ nss') setupFile? timings more
      else
        throw <| .userError "No namespace file given after --suppress-namespaces"
    | "--not-server" :: more => do
      go false nss setupFile? timings more
    | "--setup" :: more => do
      if let file :: more := more then
        go asServer nss (some file) timings more
      else
        throw <| .userError "No setup file given after --setup"
    | "--timings" :: more => do
      go asServer nss setupFile? true more
    | [mod] => pure { asServer, suppressedNamespaces := nss, setupFile?, mod, timings }
    | [mod, outFile] => pure { asServer, suppressedNamespaces := nss, setupFile?, mod, outFile := some outFile, timings }
    | other => throw <| .userError s!"Didn't understand remaining arguments: {other}"

unsafe def main (args : List String) : IO UInt32 := do
  try
    let { asServer, suppressedNamespaces, setupFile?, mod, outFile, timings } ← Config.fromArgs args
    let timer? ← if timings then some <$> Timer.new else pure none
    let start ← IO.monoNanosNow
    let code ← match outFile with
      | none =>
        go timer? asServer suppressedNamespaces setupFile? mod (← IO.getStdout)
      | some outFile =>
        if let some p := (outFile : System.FilePath).parent then
          IO.FS.createDirAll p
        IO.FS.withFile outFile .write fun h =>
          go timer? asServer suppressedNamespaces setupFile? mod (.ofHandle h)
    if let some timer := timer? then
      let stop ← IO.monoNanosNow
      IO.eprintln (← timer.report (stop - start)).compress
    pure code
  catch e =>
    if args.isEmpty then
      IO.eprintln s!"No arguments provided."
    else
      IO.eprintln s!"Error with arguments\n\t{" ".intercalate args}"
    IO.eprintln e
    IO.println helpText
    pure 1
