/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Message
import SubVerso.Compat

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

open MessageData in
partial def getTags : MessageData → List Name
  | withContext _ msg       => getTags msg
  | withNamingContext _ msg => getTags msg
  | nest _ msg              => getTags msg
  | group msg               => getTags msg
  | compose msg₁ msg₂       => getTags msg₁ ++ getTags msg₂
  | tagged n msg            => n :: getTags msg
  | .trace data msg msgs     => data.cls :: getTags msg ++ msgs.toList.flatMap getTags
  | _                       => []


def severity (msg : Message) : MessageSeverity :=
  dbg_trace "HEY! {getTags msg.data} {msg.data.hasTag (· == originalErrorTag)}"
  if msg.data.hasTag (· == originalErrorTag) then
    .error
  else msg.severity
