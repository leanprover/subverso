import Subverso.Highlighting
import Subverso.Examples
import Subverso.Examples.Env
import Lean

open Subverso.Examples (loadExamples Example)
open Lean.FromJson (fromJson?)

def assert (what : String) (cond : Unit -> Bool) : IO Unit := do
  if !(cond ()) then
    throw <| .userError what


def main : IO UInt32 := do
  IO.println "Checking that the test project generates at least some deserializable JSON"
  let examples ← loadExamples "demo"
  assert "Examples are non-empty" fun () => !examples.isEmpty
  let _exs : List (List (String × Example)) ← examples.toList.mapM fun (n, ex) => do
    let mut out := []
    match ex.getObj? with
    | .error err => throw <| IO.userError <| s!"Expected object for {n}: " ++ err
    | .ok val =>
      for ⟨k, v⟩ in val.toArray do
        match Lean.FromJson.fromJson? v with
        | .error err => throw <| IO.userError <| s!"Failed to deserialize {n}: " ++ err
        | .ok val => out := (k, val) :: out
      pure out
  pure 0
