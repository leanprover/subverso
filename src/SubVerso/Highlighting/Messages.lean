/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Message
import SubVerso.Compat
public section

namespace SubVerso.Highlighting.Messages

open Lean

private def originalErrorTag := `SubVerso.originallyError

/--
Marks a message as originally having been an error, even if it was downgraded to a warning.
-/
def originallyError (msg : MessageData) : MessageData := .tagged originalErrorTag msg

/--
Converts the errors in a message log into warnings, recording that they were originally errors for later reconstruction.
-/
def errorsToWarnings (log : MessageLog) : MessageLog :=
  SubVerso.Compat.mapMessages log fun m =>
      match m.severity with
        | MessageSeverity.error => { m with severity := MessageSeverity.warning, data := originallyError m.data }
        | _ => m

/--
Gets the severity of a message, taking recorded original severities into account.
-/
def severity (msg : Message) : MessageSeverity :=
  if msg.data.hasTag (· == originalErrorTag) then .error else msg.severity
