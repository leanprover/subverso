import SubVerso.Highlighting
import SubVerso.Examples
import SubVerso.Examples.Env
import Lean.Data.Json
import Lean.Data.NameMap

open SubVerso.Examples (loadExamples Example)
open Lean.FromJson (fromJson?)

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

def cleanupDemo : IO Unit := do
  if ← System.FilePath.pathExists "demo/lake-manifest.json" then
    IO.FS.removeFile "demo/lake-manifest.json"
  if ← System.FilePath.isDir "demo/.lake" then
    IO.FS.removeDirAll "demo/.lake"

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
