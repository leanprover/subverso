import SubVerso.Highlighting
import SubVerso.Examples
import SubVerso.Examples.Env
import Lean

open SubVerso.Examples (loadExamples Example)
open Lean.FromJson (fromJson?)

def main : IO UInt32 := do
  IO.println "Checking that the test project generates at least some deserializable JSON"
  let examples ← loadExamples "demo"
  if examples.isEmpty then
    IO.eprintln "No examples found"
    return 1
  pure 0
