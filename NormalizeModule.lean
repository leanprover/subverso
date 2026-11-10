/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Module
import SubVerso.Module.Normalize
import Lean.Data.Json

open Lean (Json)
open SubVerso
open SubVerso.Module (Module normalize)

def helpText : String :=
"Translate module JSON from subverso-extract-mod into a canonical form

Usage: subverso-normalize IN [OUT]

IN is the JSON file to normalize, and OUT is the destination. If OUT is not
specified, the result is emitted to standard output.

The result is an array of the items in source order. All shared tables are
inlined, object keys are sorted, each value is on its own line, and free
variable identifiers are renamed v1, v2, and so on, in order of first
appearance within each item. Outputs that differ only in key numbering or
free variable identifiers normalize to the same text, so they can be compared
with cmp, diff, or a JSON diff tool.

The exit code is 0 on success and 2 on errors.
"

def loadModule (path : System.FilePath) : IO Module := do
  let text ← IO.FS.readFile path
  let json ← match Json.parse text with
    | .ok json => pure json
    | .error err => throw <| IO.userError s!"Failed to parse JSON in {path}: {err}"
  match Module.fromJson? json with
  | .ok mod => pure mod
  | .error err => throw <| IO.userError s!"Failed to read module data in {path}: {err}"

partial def render (out : String) (indent : Nat) (json : Json) : String := Id.run do
  let mut out := out
  match json with
  | .arr xs =>
    if xs.isEmpty then return out ++ "[]"
    out := out ++ "["
    let mut first := true
    for x in xs do
      unless first do out := out ++ ","
      first := false
      out := line out (indent + 2)
      out := render out (indent + 2) x
    return line out indent ++ "]"
  | _ =>
    match Compat.Json.objectFields? json with
    | some fields =>
      if fields.isEmpty then return out ++ "{}"
      out := out ++ "{"
      let mut first := true
      for (k, v) in fields.qsort (fun x y => x.1 < y.1) do
        unless first do out := out ++ ","
        first := false
        out := line out (indent + 2)
        out := render (out ++ (Json.str k).compress ++ ": ") (indent + 2) v
      return line out indent ++ "}"
    | none => return out ++ json.compress
where
  line (out : String) (indent : Nat) : String := Id.run do
    let mut out := out.push '\n'
    for _ in [0:indent] do
      out := out.push ' '
    return out

def normalizeFile (input : String) (output : Option String) : IO Unit := do
  let mod ← loadModule input
  let text := render "" 0 (normalize mod) ++ "\n"
  match output with
  | some out => IO.FS.writeFile out text
  | none => IO.print text

def main (args : List String) : IO UInt32 := do
  if args.contains "--help" || args.contains "-h" then
    IO.println helpText
    return 0
  let (input, output) ← match args with
    | [input] => pure (input, none)
    | [input, output] => pure (input, some output)
    | _ =>
      IO.eprintln helpText
      return (2 : UInt32)
  try
    normalizeFile input output
    return 0
  catch e =>
    IO.eprintln e
    return (2 : UInt32)
