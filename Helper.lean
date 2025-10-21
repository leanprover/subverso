/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Compat
import SubVerso.Examples.Env
import SubVerso.Helper
import SubVerso.Signature

/-!
This is a helper to be run as a subprocess from Verso, allowing it to request
elaboration/highlighting of various sorts.

It should primarily be communicated with via the API in `SubVerso.Helper`, specifically
`send`/`sendThe` and `recieve`/`receiveThe`—see module `VersoBlog.LiterateLeanPage` in Verso for
an example.
-/

open Lean Elab Frontend
open Lean.Elab.Command (liftTermElabM elabCommand CommandElabM)
open Lean.Elab.Term (TermElabM TermElabM.run elabType elabTerm)
open SubVerso Examples Helper
open SubVerso.Highlighting (Highlighted highlight)


abbrev HelperM := ReaderT Environment IO

/--
Removes the source info from syntax, to prevent unwanted InfoTree collisions.
-/
def removeSourceInfo (stx : Syntax) : Syntax :=
  Id.run <| stx.replaceM fun
    | .node _ k args => some (.node .none k args)
    | .ident _ s x pre => some (.ident .none s x pre)
    | .atom _ i => some (.atom .none i)
    | .missing => some .missing

def handle (input output : IO.FS.Stream) : FrontendM Bool := do
  let some (req : Request) ← receive input
    | return false -- EOF between messages - terminate!
  let resp ←
    match req with
    | .term code type? =>
      try
        let stx ←
          match Parser.runParserCategory (← runCommandElabM getEnv) `term code with
          | .error e => throw <| IO.userError s!"Parse error on term: {e}"
          | .ok v => pure v
        let tyStx? ← type?.mapM fun type => do
          match Parser.runParserCategory (← runCommandElabM getEnv) `term type with
          | .error e => throw <| IO.userError s!"Parse error on type: {e}"
          | .ok v => pure v

        setMessages {} -- don't persist messages from prior elaboration tasks
        runCommandElabM <| withoutModifyingEnv <| Compat.commandWithoutAsync do
          let infoState ← getInfoState
          try
            setInfoState {}
            withEnableInfoTree true do
              let cmd ←
                if let some tyStx := tyStx? then `(#check ($(⟨stx⟩) : $(⟨removeSourceInfo tyStx⟩)))
                else `(#check $(⟨stx⟩))
              try
                elabCommand cmd
              catch
                | e =>
                  return Response.error 4 (← e.toMessageData.toString) none
              let trees := (← get).infoState.trees
              let msgs := (← get).messages
              if msgs.hasErrors then
                return Response.error 5 "Elaboration failed" <| some <| .arr <|
                  (← msgs.toArray.filter (·.severity == .error) |>.mapM (Json.str <$> ·.toString))
              let hl ← liftTermElabM <| do
                -- No messages - those are confusing here
                highlight stx #[] trees
              pure <| Response.result <| .highlighted hl
          finally
            setInfoState infoState
      catch
        | IO.Error.userError e =>
          pure <| Response.error 0 e none
        | other => throw other
    | .name code =>
      try
        let parser := Parser.ident
        let fn := Parser.andthenFn Parser.whitespace parser.fn
        let ictx := Parser.mkInputContext code "<input>"
        let env ← runCommandElabM getEnv
        let s := fn.run ictx { env, options := {} } (Parser.getTokenTable env) (Parser.mkParserState code)
        let stx? :=
          if s.hasError then
            Except.error (s.toErrorMsg ictx)
          else if Compat.String.atEnd code s.pos then
            Except.ok (s.stxStack.back)
          else
            Except.error ((s.mkError "end of input").toErrorMsg ictx)

        setMessages {} -- don't persist messages from prior elaboration tasks
        runCommandElabM <| withoutModifyingEnv <| Compat.commandWithoutAsync do
          let infoState ← getInfoState
          try
            let name ←
              match stx? with
              | .error e => throwError m!"Parse error on identifier: {e}"
              | .ok v => pure v
            setInfoState {}
            withEnableInfoTree true do

              try
                Command.runTermElabM fun _ => Compat.realizeNameNoOverloads name

              catch
                | e =>
                  return Response.error 4 (← e.toMessageData.toString) none
              let trees := (← get).infoState.trees
              let msgs := (← get).messages
              if msgs.hasErrors then
                return Response.error 5 "Elaboration failed" <| some <| .arr <|
                  (← msgs.toArray.filter (·.severity == .error) |>.mapM (Json.str <$> ·.toString))
              let hl ← liftTermElabM <| do
                -- No messages - those are confusing here
                highlight name #[] trees
              pure <| Response.result <| .highlighted hl
          finally
            setInfoState infoState
      catch
        | IO.Error.userError e =>
          pure <| Response.error 0 e none
        | other => throw other
    | .command code =>
      try
        let stx ←
          match Parser.runParserCategory (← runCommandElabM getEnv) `command code with
          | .error e => throw <| IO.userError s!"Parse error on command: {e}"
          | .ok v => pure v

        setMessages {} -- don't persist messages from prior elaboration tasks
        runCommandElabM <| Compat.commandWithoutAsync do
          let infoState ← getInfoState
          try
            setInfoState {}
            withEnableInfoTree true do
              try
                elabCommand stx
              catch
                | e =>
                  return Response.error 6 (← e.toMessageData.toString) none
              let trees := (← get).infoState.trees
              let msgs := (← get).messages
              if msgs.hasErrors then
                return Response.error 7 "Command failed" <| some <| .arr <|
                  (← msgs.toArray.filter (·.severity == .error) |>.mapM (Json.str <$> ·.toString))
              let hl ← liftTermElabM do
                highlight stx msgs.toArray trees
              pure <| Response.result <| .highlighted hl
          finally
            setInfoState infoState
      catch
        | IO.Error.userError e =>
          pure <| Response.error 0 e none
        | other => throw other
    | .signature code =>
      let parser := Parser.andthen Parser.Command.declId Parser.Command.declSig
      let fn := Parser.andthenFn Parser.whitespace parser.fn
      let ictx := Parser.mkInputContext code "<input>"
      let env ← runCommandElabM getEnv
      let s := fn.run ictx { env, options := {} } (Parser.getTokenTable env) (Parser.mkParserState code)
      let stxs? :=
        if s.hasError then
          Except.error (s.toErrorMsg ictx)
        else if Compat.String.atEnd code s.pos then
          Except.ok (s.stxStack.pop.back, s.stxStack.back)
        else
          Except.error ((s.mkError "end of input").toErrorMsg ictx)

      try
        let (name, sig) ←
          match stxs? with
          | .error e => throw <| IO.userError s!"Parse error on command: {e}"
          | .ok v => pure v

        setMessages {} -- don't persist messages from prior elaboration tasks
        runCommandElabM <| Compat.commandWithoutAsync do
          let infoState ← getInfoState
          try
            setInfoState {}
            withEnableInfoTree (m := CommandElabM) true do
              let hl ←
                try
                  let (hl, _, _, _) ← checkSignature ⟨name⟩ ⟨sig⟩
                  let msgs := (← get).messages
                  if msgs.hasErrors then
                    return Response.error 9 "Command failed" <| some <| .arr <|
                      (← msgs.toArray.filter (·.severity == .error) |>.mapM (Json.str <$> ·.toString))
                  pure hl
                catch
                  | e =>
                    return Response.error 8 (← e.toMessageData.toString) none
              return Response.result <| .highlighted hl
          finally
            setInfoState infoState
      catch
        | IO.Error.userError e =>
          pure <| Response.error 0 e none
        | other => throw other
    | .exit =>
      return false
  send output resp
  pure true

def serve (input output : IO.FS.Stream) : FrontendM UInt32 := do
  repeat
    if !(← handle input output) then break
  return 0

unsafe def main : (args : List String) → IO UInt32
  | [mod] => do
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
      let env ← Compat.importModules imports {}
      let pctx : Context := {inputCtx := ictx}

      let commandState : Command.State := { env, maxRecDepth := defaultMaxRecDepth, messages := msgs }
      let scopes :=
        let sc := commandState.scopes[0]!
        {sc with opts := sc.opts.setBool `pp.tagAppFns true } :: commandState.scopes.tail!
      let commandState := { commandState with scopes }

      let cmdPos := parserState.pos
      let cmdSt ← IO.mkRef {commandState, parserState, cmdPos}
      processCommands pctx cmdSt

      return (← (serve (← IO.getStdin) (← IO.getStdout)) pctx cmdSt)

    catch e =>
      IO.eprintln s!"error finding highlighted code: {toString e}"
      return 2
  | other => do
    IO.eprintln s!"Didn't understand args: {other}"
    pure 1
