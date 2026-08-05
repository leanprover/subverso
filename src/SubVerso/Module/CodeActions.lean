/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import SubVerso.Compat
public import SubVerso.Module

public section

open Lean Elab

namespace SubVerso.Module

/-- Converts an LSP text edit to a suggested edit with absolute document positions. -/
def suggestedEditOfTextEdit (text : FileMap) (edit : Lsp.TextEdit) : SuggestedEdit :=
  let start := text.lspPosToUtf8Pos edit.range.start
  let stop := text.lspPosToUtf8Pos edit.range.end
  { range := (text.toPosition start, text.toPosition stop),
    utf8Range := (start.byteIdx, stop.byteIdx),
    newText := edit.newText }

/--
Extracts the code actions offered in a module after it has been elaborated. Each command's info
trees and messages are presented to the language server's code action handlers against the final
command state, and every action's edit is computed. Each returned action is anchored at the range
of the command where it is offered. On toolchains without code action support, the result is
empty.
-/
def extractCodeActions (text : FileMap) (fileName : String) (mod : Name)
    (finalState : Command.State)
    (items : Array Compat.Frontend.FrontendItem) : IO (Array CodeAction) := do
  let docMeta := Compat.CodeAction.mkDocumentMeta s!"file://{fileName}" mod text
  let eligible := items.filter fun item =>
    !Parser.isTerminalCommand item.commandSyntax && item.info.size == 1
  let snaps ← eligible.mapM (Compat.CodeAction.mkSnapshot finalState)
  let doc ← Compat.CodeAction.mkEditableDocument docMeta snaps.toList
  let ctx ← Compat.CodeAction.mkRequestContext doc
  let mut out := #[]
  for item in eligible do
    let some rawRange := item.commandSyntax.getRange?
      | continue
    let anchorRange := (text.toPosition rawRange.start, text.toPosition rawRange.stop)
    let anchorUtf8 := (rawRange.start.byteIdx, rawRange.stop.byteIdx)
    let params : Lsp.CodeActionParams := {
      textDocument := ⟨docMeta.uri⟩,
      range := {
        start := text.utf8PosToLspPos rawRange.start,
        «end» := text.utf8PosToLspPos rawRange.stop
      }
    }
    let actions ←
      try
        Compat.CodeAction.codeActionsAt params |>.runInIO ctx
      catch e =>
        IO.eprintln s!"Code actions failed at {fileName}:{anchorRange.1.line}: {e}"
        pure #[]
    for eager in actions do
      let action ←
        if eager.edit?.isSome then pure eager
        else
          try
            Compat.CodeAction.resolveCodeAction eager |>.runInIO ctx
          catch e =>
            IO.eprintln s!"Code action '{eager.title}' failed to compute its edit: {e}"
            pure eager
      let some edit := action.edit?
        | continue
      let edits := Compat.CodeAction.workspaceEditTextEdits edit |>.map (suggestedEditOfTextEdit text)
      unless edits.isEmpty do
        out := out.push {
          range := anchorRange,
          utf8Range := anchorUtf8,
          title := action.title,
          kind? := action.kind?,
          isPreferred := action.isPreferred?.getD false,
          edits
        }
  let mut seen : Array String := #[]
  let mut deduped := #[]
  for action in out do
    let key := Json.mkObj [
      ("title", ToJson.toJson action.title),
      ("edits", ToJson.toJson action.edits)
    ] |>.compress
    unless seen.contains key do
      seen := seen.push key
      deduped := deduped.push action
  return deduped
