import SubVerso.Highlighting
import SubVerso.Examples
import SubVerso.Examples.Env
import SubVerso.Examples.Slice
import SubVerso.Module
import SubVerso.Helper.Netstring
import Lean.Data.Json
import Lean.Data.NameMap

open SubVerso.Examples (loadExamples Example)
open SubVerso.Module (ModuleItem)
open Lean.FromJson (fromJson?)

open SubVerso

section
open Lean Elab Command
open SubVerso.Examples.Slice

elab "#test_slicing" s:str out:ident c:command : command => do
  let {original := _, residual, sliced} ← sliceSyntax c

  let mut log := ""

  log := log ++ s!"Original:\n{Syntax.prettyPrint c}\n"
  log := log ++ s!"Residual:\n{Syntax.prettyPrint residual}\n"
  for (s, stx) in sliced.toArray do
    log := log ++ s!"Slice {s}:\n{Syntax.prettyPrint stx}\n"

  let use := s.getString
  if let some stx := sliced[use]? then
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
  let _ := [1, 2/- !! begin foo-/, 3/- !! end foo-/]
  pure ()

/-- Lean versions 4.10.0 and earlier had some issues with Syntax.prettyPrint. They were fixed in 4.11, but as that's not really what's being tested, both are OK. -/
def expectedLogOld :=
  "Original:\ndef heya : IO Unit := do\n  IO.print \"Hey\"\n  -- !! begin foo\n  IO.println \" there\"\n  /- Bigger comment\n  -/\n  -- !! end foo\n  let x := 33 -- !! begin foo\n  if x > 3 then pure () -- !! end foo\n  if x == 3 /-\n    !! begin foo\n  -/ || true /- !! end foo -/ then pure ()\n  let _ := [1, 2/- !! begin foo-/, 3/- !! end foo-/]\n  pure ( ) \nResidual:\ndef heya : IO Unit := do\n  IO.print \"Hey\"\n  let x := 33 \n  if x == 3  then pure ()\n  let _ := [1, 2]\n  pure ( ) \nSlice foo:\ndef heya : IO Unit := do\n  IO.print \"Hey\"\n  IO.println \" there\"\n  /- Bigger comment\n  -/\n  let x := 33 \n  if x > 3 then pure () \n  if x == 3  || true  then pure ()\n  let _ := [1, 2, 3]\n  pure ( ) \n"


def expectedLog :=
  "Original:\ndef heya : IO Unit := do\n  IO.print \"Hey\"\n  -- !! begin foo\n  IO.println \" there\"\n  /- Bigger comment\n  -/\n  -- !! end foo\n  let x := 33 -- !! begin foo\n  if x > 3 then pure () -- !! end foo\n  if x == 3 /-\n    !! begin foo\n  -/ || true /- !! end foo -/ then pure ()\n  let _ := [1, 2/- !! begin foo-/, 3/- !! end foo-/]\n  pure ()\nResidual:\ndef heya : IO Unit := do\n  IO.print \"Hey\"\n  let x := 33 \n  if x == 3  then pure ()\n  let _ := [1, 2]\n  pure ()\nSlice foo:\ndef heya : IO Unit := do\n  IO.print \"Hey\"\n  IO.println \" there\"\n  /- Bigger comment\n  -/\n  let x := 33 \n  if x > 3 then pure () \n  if x == 3  || true  then pure ()\n  let _ := [1, 2, 3]\n  pure ()\n"

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
  if ← System.FilePath.isDir (demo / "lake-packages") then
    IO.FS.removeDirAll (demo / "lake-packages")
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

open Lean in
def checkHasSorry (examples : NameMap (NameMap Example)) : IO Unit := do
  IO.println "Making sure the `hasSorry example has a sorry"
  let demo ← examples.find? `Demo |>.map pure |>.getD (do IO.eprintln "Demo not found"; IO.Process.exit 1)
  let hasSorry ← demo.find? `hasSorry  |>.map pure |>.getD (do IO.eprintln "hasSorry not found"; IO.Process.exit 1)
  if hasSorry.messages == [(.warning, "declaration uses 'sorry'\n")] then pure ()
  else
    IO.eprintln s!"Expected a sorry warning, got {repr hasSorry.messages}"
    IO.Process.exit 1

open Lean in
def checkIsLinted (examples : NameMap (NameMap Example)) : IO Unit := do
  IO.println "Making sure the linted example is linted"
  let demo ← examples.find? `Demo |>.map pure |>.getD (do IO.eprintln "Demo not found"; IO.Process.exit 1)
  let hasSorry ← demo.find? `linted  |>.map pure |>.getD (do IO.eprintln "linted not found"; IO.Process.exit 1)
  if let [(.warning, str)] := hasSorry.messages then
    -- The phrasing varies a bit in Lean versions, but this is the important part
    if "unused variable `x`".isPrefixOf str then
      return ()

  IO.eprintln s!"Expected a linter warning, got {repr hasSorry.messages}"
  IO.Process.exit 1

open SubVerso.Helper in
def testNetstring (str : String) : IO Unit := do
  let buf ← IO.mkRef {}
  let stream := IO.FS.Stream.ofBuffer buf
  writeNetstring stream str.toUTF8
  buf.modify ({· with pos := 0})
  let some bytes ← readNetstring stream
    | throw <| .userError "Didn't read netstring (unexpected EOF)"
  let str2 := Compat.decodeUTF8 bytes
  if str == str2 then pure ()
  else throw <| .userError s!"Mismatch: expected '{str}' but got '{str2}'"

def testNetstrings := do
  testNetstring ""
  testNetstring "abc"
  testNetstring "abc{}\n"
  let mut longStr := "hello\n"
  for i in [0:100] do
    longStr := s!"{i}({longStr}{longStr})"
  testNetstring longStr

-- Loads a module. To work well, it really should lock the toolchain file, but that's not available
-- in all targeted versions, so it's just part of these tests. See Verso for a version to use in
-- documents.
open System in
def loadModuleContent
    (projectDir : String) (mod : String)
    (overrideToolchain : Option String := none) :
    IO (Array ModuleItem) := do

  let projectDir : FilePath := projectDir

  -- Validate that the path is really a Lean project
  let lakefile := projectDir / "lakefile.lean"
  let lakefile' := projectDir / "lakefile.toml"
  if !(← lakefile.pathExists) && !(← lakefile'.pathExists) then
    throw <| .userError s!"Neither {lakefile} nor {lakefile'} exist, couldn't load project"

  let toolchain ←
    match overrideToolchain with
    | none =>
      let toolchainfile := projectDir / "lean-toolchain"
      let toolchain ← do
          if !(← toolchainfile.pathExists) then
            throw <| .userError s!"File {toolchainfile} doesn't exist, couldn't load project"
          pure (← IO.FS.readFile toolchainfile).trim
    | some override => pure override

  -- Kludge: remove variables introduced by Lake. Clearing out DYLD_LIBRARY_PATH and
  -- LD_LIBRARY_PATH is useful so the version selected by Elan doesn't get the wrong shared
  -- libraries.
  let lakeVars :=
    #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
      "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
      "LEAN_GITHASH",
      "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]


  let cmd := "elan"
  let args := #["run", "--install", toolchain, "lake", "exe", "subverso-extract-mod", mod]
  let res ← IO.Process.output {
    cmd, args, cwd := projectDir
    -- Unset Lake's environment variables
    env := lakeVars.map (·, none)
  }
  if res.exitCode != 0 then reportFail projectDir cmd args res
  let output := res.stdout

  let .ok (.arr json) := Lean.Json.parse output
    | throw <| IO.userError s!"Expected JSON array"
  match json.mapM fromJson? with
  | .error err =>
    throw <| IO.userError s!"Couldn't parse JSON from output file: {err}\nIn:\n{json}"
  | .ok vals =>
    pure vals


where
  decorateOut (name : String) (out : String) : String :=
    if out.isEmpty then "" else s!"\n{name}:\n{out}\n"
  reportFail {α} (projectDir : FilePath) (cmd : String) (args : Array String) (res : IO.Process.Output) : IO α := do
    IO.eprintln <|
      "Build process failed." ++
      "\nCWD: " ++ projectDir.toString ++
      "\nCommand: " ++ cmd ++
      "\nArgs: " ++ repr args ++
      "\nExit code: " ++ toString res.exitCode ++
      "\nstdout: " ++ res.stdout ++
      "\nstderr: " ++ res.stderr

    throw <| .userError <|
      "Build process failed." ++
      decorateOut "stdout" res.stdout ++
      decorateOut "stderr" res.stderr


def desiredAnchors : List (String × String) := [
  ("cons", "  | cons : Nat → NatList → NatList\n"),
  ("NatList", "inductive NatList where\n  | nil\n  | cons : Nat → NatList → NatList\n")
]
def desiredProofs : List (String × String) := [
  ("base", "case cons =>\n  ys: NatList\n  a✝¹: Nat\n  a✝: NatList\n  a_ih✝: ∀ (zs : NatList), a✝.append (ys.append zs) = (a✝.append ys).append zs\n⊢ ∀ (zs : NatList), (cons a✝¹ a✝).append (ys.append zs) = ((cons a✝¹ a✝).append ys).append zs"),
  ("ind", "case nil =>\n  ys: NatList\n⊢ ∀ (zs : NatList), nil.append (ys.append zs) = (nil.append ys).append zs\n\ncase cons =>\n  ys: NatList\n  a✝¹: Nat\n  a✝: NatList\n  a_ih✝: ∀ (zs : NatList), a✝.append (ys.append zs) = (a✝.append ys).append zs\n⊢ ∀ (zs : NatList), (cons a✝¹ a✝).append (ys.append zs) = ((cons a✝¹ a✝).append ys).append zs"),
  ("doubleIntro", "  xs: NatList\n  ys: NatList\n⊢ ∀ (zs : NatList), xs.append (ys.append zs) = (xs.append ys).append zs"),
  ("step", "case cons =>\n  ys: NatList\n  a✝¹: Nat\n  a✝: NatList\n  a_ih✝: ∀ (zs : NatList), a✝.append (ys.append zs) = (a✝.append ys).append zs\n⊢ ∀ (zs : NatList), cons a✝¹ (a✝.append (ys.append zs)) = cons a✝¹ ((a✝.append ys).append zs)"),
  ("ih", "case cons =>\n  ys: NatList\n  a✝¹: Nat\n  a✝: NatList\n  ih: ∀ (zs : NatList), a✝.append (ys.append zs) = (a✝.append ys).append zs\n⊢ ∀ (zs : NatList), cons a✝¹ (a✝.append (ys.append zs)) = cons a✝¹ ((a✝.append ys).append zs)"),
  ("done", "")
]

def desiredAltProofs : List (String × String × String) := [
  ("A",
   "| inl hp =>",
   "case inl =>
  p: Prop
  q: Prop
  hp: p
⊢ q ∨ p"),
  ("A'",
   "| inl hp =>",
   "case inl =>
  p: Prop
  q: Prop
  hp: p
⊢ q ∨ p"),
  ("A''",
   "| inl hp =>",
   "case inl =>
  p: Prop
  q: Prop
  hp: p
⊢ q ∨ p"),
  ("A'''",
   "apply Or.inr",
   "case inl.h =>
  p: Prop
  q: Prop
  hp: p
⊢ p"),
  ("B",
   "| inr hq =>",
   "case inr =>
  p: Prop
  q: Prop
  hq: q
⊢ q ∨ p"),
  ("B'",
   "| inr hq =>",
   "case inr =>
  p: Prop
  q: Prop
  hq: q
⊢ q ∨ p"),
  ("B''",
   "| inr hq =>",
   "case inr =>
  p: Prop
  q: Prop
  hq: q
⊢ q ∨ p"),
  ("B'''",
   "apply Or.inl",
   "case inr.h =>
  p: Prop
  q: Prop
  hq: q
⊢ q"),
  ("Arr",
   "=>",
   "case inr =>
  p: Prop
  q: Prop
  hq: q
⊢ q ∨ p
case inl =>
  p: Prop
  q: Prop
  hp: p
⊢ q ∨ p"),
  ("Two",
   "simp [*]",
   "")
]

def main : IO UInt32 := do
  IO.println "Checking the slice log"
  -- The pretty-printer used to show the modified syntax had some bug-fixes. We can just check both.
  if sliceLog != expectedLog && sliceLog != expectedLogOld then
    IO.println "Mismatch between expected:"
    IO.println expectedLog
    IO.println "and actual:"
    IO.println sliceLog
    return 1

  IO.println "Checking that the TOML project will load"
  cleanupDemo (demo := "demo-toml")
  let examplesToml ← loadExamples "demo-toml"
  if examplesToml.isEmpty then
    IO.eprintln "No examples found"
    return 1
  else IO.println s!"Found {proofCount examplesToml} proofs"

  IO.println "Checking anchor test file in TOML project"
  cleanupDemo (demo := "demo-toml")
  let anchorMod := (← loadModuleContent "demo-toml" "Anchors").map (·.code) |>.foldl (· ++ ·) (.empty)
  match anchorMod.anchored with
  | .error e => IO.eprintln e; return 1
  | .ok {code:=_, anchors, proofStates} =>
    for k in desiredAnchors.map (·.1) do
      unless anchors.contains k do IO.eprintln s!"Missing anchor '{k}'"; return 1
    for k in desiredProofs.map (·.1) do
      unless proofStates.contains k do IO.eprintln s!"Missing proofs state '{k}'"; return 1
    for ⟨a, hl⟩ in anchors.toArray do
      match desiredAnchors.lookup a with
      | none => IO.eprintln s!"Unwanted anchor '{a}'"; return 1
      | some s =>
        if s ≠ hl.toString then
          IO.eprintln s!"For anchor '{a}' expected\n{repr s}\nbut got\n{repr hl.toString}"; return 1
    for ⟨p, y⟩ in proofStates.toArray do
      if let .tactics info _s _e _ := y then
        let g := info.map (·.toString) |>.toList |> String.intercalate "\n\n"
        match desiredProofs.lookup p with
        | none => IO.eprintln s!"Unwanted proof state '{p}'"; return 1
        | some y' =>
          if g ≠ y' then
            IO.eprintln s!"For proof state '{p}' expected\n{repr y'}\nbut got\n{repr g}"; return 1
      else
        IO.eprintln "Got non-tactic {hl y}"; return 1

  IO.println "Checking that the test project generates at least some deserializable JSON with 4.3.0"
  cleanupDemo
  let examples ← loadExamples "demo"
  if examples.isEmpty then
    IO.eprintln "No examples found"
    return 1
  checkVersion "4.3.0" examples
  checkHasSorry examples
  checkIsLinted examples
  let proofCount1 := proofCount examples
  IO.println s!"Found {proofCount1} proofs "

  IO.println "Checking that the test project generates at least some deserializable JSON with 4.8.0"
  cleanupDemo
  let examples' ← loadExamples "demo" (overrideToolchain := some "leanprover/lean4:v4.8.0")
  if examples'.isEmpty then
    IO.eprintln "No examples found with later toolchain"
    return 1
  checkVersion "4.8.0" examples'
  checkHasSorry examples'
  checkIsLinted examples'
  let proofCount2 := proofCount examples'
  IO.println s!"Found {proofCount2} proofs "

  IO.println "Checking that the test project generates at least some deserializable JSON with 4.10.0"
  cleanupDemo
  let examples'' ← loadExamples "demo" (overrideToolchain := some "leanprover/lean4:4.10.0")
  if examples''.isEmpty then
    IO.eprintln "No examples found with later toolchain"
    return 1
  checkVersion "4.10.0" examples''
  checkHasSorry examples''
  checkIsLinted examples''
  let proofCount3 := proofCount examples''
  IO.println s!"Found {proofCount2} proofs "

  if proofCount1 != proofCount2 || proofCount2 != proofCount3 then
    IO.eprintln "Example proof count mismatch"
    return 1

  IO.println "Checking proof states for induction/cases alts"
  let myToolchain := (← IO.FS.readFile "lean-toolchain").trim
  cleanupDemo "small-tests"
  discard do
    try
      IO.Process.run {cmd := "lake", args := #["update", "--keep-toolchain"], cwd := "./small-tests"}
    catch _ =>
      IO.Process.run {cmd := "lake", args := #["update"], cwd := "./small-tests"}

  let items ← loadModuleContent "small-tests" "Small.TacticAlts" (overrideToolchain := myToolchain)
  let content := items.map (·.code) |>.foldl (· ++ ·) (.empty)
  match content.anchored with
    | .error e => IO.eprintln e; return 1
    | .ok {code:=_, anchors:=_, proofStates} =>
      let mut errors := false
      for (name, code, state) in desiredAltProofs do
        if let some hl := proofStates.get? name then
          let .tactics goals _ _ hl := hl
            | IO.eprintln s!"Proof state '{name}' not a proof state: {repr hl}"; errors := true
          if hl.toString != code then
            IO.eprintln s!"Proof state '{name}': expected {repr code} but got {repr hl.toString}"; errors := true
          let goalString := "\n".intercalate (goals.map (·.toString) |>.toList)
          if state != goalString then
            IO.eprintln s!"Proof state '{name}': expected {repr state} but got {repr goalString}"; errors := true
        else
          IO.eprintln "Not found: proof state '{name}'"; errors := true
      if errors then return 1
  IO.println "Proof states for induction/cases alts OK"

  pure 0
