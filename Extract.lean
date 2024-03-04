import Lean
import SubVerso.Examples.Env

open Lean
open SubVerso.Examples

def main : (args : List String) → IO UInt32
  | [mod, outFile] => do
    try
      initSearchPath (← findSysroot)
      let env ← importModules #[{module := mod.toName, runtimeOnly := false}] {}
      let modExamples := highlighted.getState env
      let exJson := Json.mkObj <| modExamples.toList.map (fun p => {p with fst := p.fst.toString (escape := false)})
      IO.println s!"Processed {modExamples.size} examples"
      if let some p := (outFile : System.FilePath).parent then
        IO.FS.createDirAll p
      IO.FS.writeFile outFile (toString exJson ++ "\n")
      return 0
    catch e =>
      IO.eprintln s!"error finding highlighted code: {toString e}"
      return 2
  | other => do
    IO.eprintln s!"Didn't understand args: {other}"
    pure 1
