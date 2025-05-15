/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Message

namespace SubVerso.Highlighting.Messages

open Lean

/--
Marks a message as originally having been an error, even if it was downgraded to a warning.
-/
def originallyError (msg : MessageData) : MessageData := .tagged `SubVerso.originallyError msg

/--
Converts the errors in a message log into warnings, recording that they were originally errors for later reconstruction.
-/
def errorsToWarnings (log : MessageLog) : MessageLog :=
  { msgs := log.msgs.map fun m =>
      match m.severity with
        | MessageSeverity.error => { m with severity := MessageSeverity.warning, data := originallyError m.data }
        | _ => m
  }

def severity (msg : Message) : MessageSeverity :=
  if msg.data.hasTag (· == `SubVerso.originallyError) then .error else msg.severity
