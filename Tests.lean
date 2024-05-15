import SubVerso.Highlighting
import SubVerso.Examples
import SubVerso.Examples.Env
import SubVerso.Examples.Slice
import Lean.Data.Json
import Lean.Data.NameMap

open SubVerso.Examples (loadExamples Example)
open Lean.FromJson (fromJson?)


section
open Lean Elab Command
open SubVerso.Examples.Slice

elab "#test_slicing" s:str out:ident c:command : command => do
  let {original, residual, sliced} ← sliceSyntax c

  let mut log := ""

  log := log ++ s!"Original:\n{Syntax.prettyPrint c}"
  log := log ++ s!"Residual:\n{Syntax.prettyPrint residual}"
  for (s, stx) in sliced.toArray do
    log := log ++ s!"Slice {s}:\n{Syntax.prettyPrint stx}"

  let use := s.getString
  if let some stx := sliced.find? use then
    elabCommand stx
  else
    logInfo m!"Slice '{use}' not found"
    elabCommand residual
  elabCommand <| ← `(def $out := $(quote log))

set_option pp.rawOnError true in
#test_slicing "foo" sliceLog
def heya : IO Unit := do
  IO.print "Hey"
  -- !! begin foo
  IO.println " there"
  /- Bigger comment
  -/
  -- !! end foo
  let x := 33 -- !! begin foo
  if x > 3 then pure () -- !! end foo
  if x == 3 /-
    !! begin foo
  -/ || true /- !! end foo -/ then pure ()
  let x := [1, 2/- !! begin foo-/, 3/- !! end foo-/]
  pure ()

def expectedLog :=
  "Original:\ndef heya : IO Unit := do\n  IO.print \"Hey\"\n  -- !! begin foo\n  IO.println \" there\"\n  /- Bigger comment\n  -/\n  -- !! end foo\n  let x := 33 -- !! begin foo\n  if x > 3 then pure () -- !! end foo\n  if x == 3 /-\n    !! begin foo\n  -/ || true /- !! end foo -/ then pure ()\n  let x := [1, 2/- !! begin foo-/, 3/- !! end foo-/]\n  pure ( ) Residual:\ndef heya : IO Unit := do\n  IO.print \"Hey\"\n  let x := 33 \n  if x == 3  then pure ()\n  let x := [1, 2]\n  pure ( ) Slice foo:\ndef heya : IO Unit := do\n  IO.print \"Hey\"\n  IO.println \" there\"\n  /- Bigger comment\n  -/\n  let x := 33 \n  if x > 3 then pure () \n  if x == 3  || true  then pure ()\n  let x := [1, 2, 3]\n  pure ( ) "

end

open Lean in
def exampleArray (examples : NameMap (NameMap α)) : Array α := Id.run do
  let mut exs := #[]
  for (_, inner) in examples do
    for (_, x) in inner do
      exs := exs.push x
  exs

open Lean in
def findVersionString (examples : NameMap (NameMap Example)) : Option String := do
  let demo ← examples.find? `Demo
  let version ← demo.find? `version
  let [(.information, str)] := version.messages
    | none
  str.trim |>.drop 1 |>.dropRight 1

namespace SubVerso

partial
def Highlighting.Highlighted.countProofStates (hl : Highlighting.Highlighted) : Nat :=
  match hl with
  | .seq hls =>
    hls.map countProofStates |>.foldr (· + · ) 0
  | .span _ hl' =>
    hl'.countProofStates
  | .tactics _ _ _ hl' =>
    hl'.countProofStates + 1
  | _ => 0

namespace Examples

def Example.countProofStates (e : Example) : Nat :=
  e.highlighted.map (·.countProofStates) |>.foldl (· + ·) 0

end Examples
end SubVerso

def cleanupDemo (demo : System.FilePath := "demo") : IO Unit := do
  if ← System.FilePath.pathExists (demo / "lake-manifest.json") then
    IO.FS.removeFile (demo / "lake-manifest.json")
  if ← System.FilePath.isDir (demo / ".lake") then
    IO.FS.removeDirAll (demo / ".lake")

open Lean in
def proofCount (examples : NameMap (NameMap Example)) : Nat := Id.run do
  let mut n := 0
  for e in exampleArray examples do
    n := n + e.countProofStates
  n

open Lean in
def checkVersion (expected : String) (examples : NameMap (NameMap Example)) : IO Unit := do
  let v := findVersionString examples
  IO.println s!"Reported version {v}"
  if v != some expected then
    IO.eprintln "Unexpected version!"
    IO.Process.exit 1
  pure ()

def main : IO UInt32 := do
  IO.println "Checking the slice log"
  if sliceLog != expectedLog then
    IO.println "Mismatch between expected:"
    IO.println sliceLog
    IO.println "and actual:"
    IO.println expectedLog

  IO.println "Checking that the TOML project will load"
  cleanupDemo (demo := "demo-toml")
  let examplesToml ← loadExamples "demo-toml"
  if examplesToml.isEmpty then
    IO.eprintln "No examples found"
    return 1
  else IO.println s!"Found {proofCount examplesToml} proofs"

  IO.println "Checking that the test project generates at least some deserializable JSON"
  cleanupDemo
  let examples ← loadExamples "demo"
  if examples.isEmpty then
    IO.eprintln "No examples found"
    return 1
  checkVersion "4.3.0" examples
  let proofCount1 := proofCount examples
  IO.println s!"Found {proofCount1} proofs "
  IO.println "Checking that the test project generates at least some deserializable JSON with a newer toolchain"
  cleanupDemo
  let examples' ← loadExamples "demo" (overrideToolchain := some "leanprover/lean4:nightly-2024-04-25")
  if examples'.isEmpty then
    IO.eprintln "No examples found with later toolchain"
    return 1
  checkVersion "4.8.0-nightly-2024-04-25" examples'
  let proofCount2 := proofCount examples'
  IO.println s!"Found {proofCount2} proofs "

  if proofCount1 != proofCount2 then
    IO.eprintln "Example proof count mismatch"
    return 1
  pure 0
