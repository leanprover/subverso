import SubVerso.Highlighting
import SubVerso.Examples
import SubVerso.Examples.Env
import Lean

open SubVerso.Examples (loadExamples Example)
open Lean.FromJson (fromJson?)

def assert (what : String) (cond : Unit -> Bool) : IO Unit := do
  if !(cond ()) then
    throw <| .userError what


def main : IO UInt32 := do
  IO.println "Checking that the test project generates at least some deserializable JSON"
  let examples ← loadExamples "demo"
  assert "Examples are non-empty" fun () => !examples.isEmpty
  pure 0
