import SubVerso.Highlighting
import SubVerso.Examples
import SubVerso.Examples.Env
import SubVerso.Module
import SubVerso.Helper.Netstring
import Lean.Data.Json
import Lean.Data.NameMap

open SubVerso.Examples (loadExamples Example)
open SubVerso.Module (ModuleItem)
open Lean.FromJson (fromJson?)

open SubVerso

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
  Compat.String.trim str |>
  (Compat.String.drop · 1) |>
  (Compat.String.dropRight · 1)

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

def lakeVars :=
  #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
    "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
    "LEAN_GITHASH",
    "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]

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
    | none => do
      let toolchainfile := projectDir / "lean-toolchain"
      if !(← toolchainfile.pathExists) then
        throw <| .userError s!"File {toolchainfile} doesn't exist, couldn't load project"
      pure <| Compat.String.trim (← IO.FS.readFile toolchainfile)
    | some override => pure override

  -- Kludge: remove variables introduced by Lake. Clearing out DYLD_LIBRARY_PATH and
  -- LD_LIBRARY_PATH is useful so the version selected by Elan doesn't get the wrong shared
  -- libraries.


  let cmd := "elan"
  let args := #["run", "--install", toolchain, "lake", "exe", "subverso-extract-mod", mod]
  let res ← IO.Process.output {
    cmd, args, cwd := projectDir
    -- Unset Lake's environment variables
    env := lakeVars.map (·, none)
  }
  if res.exitCode != 0 then reportFail projectDir cmd args res
  let output := res.stdout

  let .ok json := Lean.Json.parse output
    | throw <| IO.userError s!"Expected JSON array"
  match Module.Module.fromJson? json with
  | .error err =>
    throw <| IO.userError s!"Couldn't parse JSON from output file: {err}\nIn:\n{json}"
  | .ok m =>
    pure m.items


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
  ("base", "case cons\nys : NatList\na✝¹ : Nat\na✝ : NatList\na_ih✝ : ∀ (zs : NatList), a✝.append (ys.append zs) = (a✝.append ys).append zs\n⊢ ∀ (zs : NatList), (cons a✝¹ a✝).append (ys.append zs) = ((cons a✝¹ a✝).append ys).append zs"),
  ("ind", "case nil\nys : NatList\n⊢ ∀ (zs : NatList), nil.append (ys.append zs) = (nil.append ys).append zs\n\ncase cons\nys : NatList\na✝¹ : Nat\na✝ : NatList\na_ih✝ : ∀ (zs : NatList), a✝.append (ys.append zs) = (a✝.append ys).append zs\n⊢ ∀ (zs : NatList), (cons a✝¹ a✝).append (ys.append zs) = ((cons a✝¹ a✝).append ys).append zs"),
  ("doubleIntro", "xs : NatList\nys : NatList\n⊢ ∀ (zs : NatList), xs.append (ys.append zs) = (xs.append ys).append zs"),
  ("step", "case cons\nys : NatList\na✝¹ : Nat\na✝ : NatList\na_ih✝ : ∀ (zs : NatList), a✝.append (ys.append zs) = (a✝.append ys).append zs\n⊢ ∀ (zs : NatList), cons a✝¹ (a✝.append (ys.append zs)) = cons a✝¹ ((a✝.append ys).append zs)"),
  ("ih", "case cons\nys : NatList\na✝¹ : Nat\na✝ : NatList\nih : ∀ (zs : NatList), a✝.append (ys.append zs) = (a✝.append ys).append zs\n⊢ ∀ (zs : NatList), cons a✝¹ (a✝.append (ys.append zs)) = cons a✝¹ ((a✝.append ys).append zs)"),
  ("done", "")
]

-- The third component lists the acceptable goal states. More than one is allowed because the case
-- tag emitted for the goal of e.g. `apply Or.inr` changed across Lean versions: older toolchains
-- tag it `inl.h` (after the constructor's field), while starting with version 4.31.0-rc1 they tag
-- it just `inl`.
def desiredAltProofs : List (String × String × List String) := [
  ("A",
   "| inl hp =>",
   ["case inl
p : Prop
q : Prop
hp : p
⊢ q ∨ p"]),
  ("A'",
   "| inl hp =>",
   ["case inl
p : Prop
q : Prop
hp : p
⊢ q ∨ p"]),
  ("A''",
   "| inl hp =>",
   ["case inl
p : Prop
q : Prop
hp : p
⊢ q ∨ p"]),
  ("A'''",
   "apply Or.inr",
   ["case inl.h
p : Prop
q : Prop
hp : p
⊢ p",
    "case inl
p : Prop
q : Prop
hp : p
⊢ p"]),
  ("B",
   "| inr hq =>",
   ["case inr
p : Prop
q : Prop
hq : q
⊢ q ∨ p"]),
  ("B'",
   "| inr hq =>",
   ["case inr
p : Prop
q : Prop
hq : q
⊢ q ∨ p"]),
  ("B''",
   "| inr hq =>",
   ["case inr
p : Prop
q : Prop
hq : q
⊢ q ∨ p"]),
  ("B'''",
   "apply Or.inl",
   ["case inr.h
p : Prop
q : Prop
hq : q
⊢ q",
    "case inr
p : Prop
q : Prop
hq : q
⊢ q"]),
  ("Arr",
   "=>",
   ["case inr
p : Prop
q : Prop
hq : q
⊢ q ∨ p
case inl
p : Prop
q : Prop
hp : p
⊢ q ∨ p"]),
  ("Two",
   "simp [*]",
   [""])
]

partial def copyRecursively (src tgt : System.FilePath) (visit : String → Bool) : IO Unit := do
  if (← src.isDir) then
    for ⟨_, name⟩ in ← src.readDir do
      if visit name then
        IO.FS.createDirAll tgt
        copyRecursively (src / name) (tgt / name) visit
  else
    let data ← IO.FS.readBinFile src
    IO.FS.writeBinFile tgt data

/--
The root under which per-toolchain build directories are created. Each demo project is built in
`<buildRoot>/<toolchain>/<project>`, so builds under different Lean versions don't share (and
corrupt) a single `.lake`, and each directory can be cached independently in CI. Overridable via
`SUBVERSO_TEST_BUILD_ROOT` so CI can point its cache at a known location.
-/
def buildRoot : IO System.FilePath := do
  pure <| (← IO.getEnv "SUBVERSO_TEST_BUILD_ROOT").getD ".builds"

/--
Turns a toolchain string (e.g. `leanprover/lean4:v4.8.0`) into a safe single path component.
-/
def sanitizeToolchain (toolchain : String) : String :=
  toolchain.map fun c => if c.isAlphanum || c == '.' then c else '-'

/--
Reads a project's pinned toolchain from its `lean-toolchain` file.
-/
def projectToolchain (project : System.FilePath) : IO String := do
  let f := project / "lean-toolchain"
  if !(← f.pathExists) then
    throw <| .userError s!"File {f} doesn't exist, can't determine the project's toolchain"
  pure <| Compat.String.trim (← IO.FS.readFile f)

/--
Generates the demodulized SubVerso source tree once, returning its path. This is the path
dependency (`require subverso from "no-mod"`) shared, by copying, into every per-toolchain build
directory's `no-mod`. It is regenerated deterministically from the current source on each run, so a
source change is reflected in the dependency build.
-/
def prepareDemodulizedSource : IO System.FilePath := do
  let src := (← buildRoot) / "no-mod-src"
  IO.println "Generating demodulized SubVerso source for the test projects"
  -- Regenerate from scratch so removed source files don't linger.
  if ← src.pathExists then IO.FS.removeDirAll src
  IO.FS.createDirAll src
  copyRecursively "." src
    (fun f => !f.startsWith "." && !(f.startsWith "demo" || f.startsWith "small-tests") && f != "lake-manifest.json")
  discard <| IO.Process.run {cmd := "python3", args := #["demodulize.py", src.toString]}
  pure src

/--
Prepares a per-toolchain build directory for `project` and returns it. The project's own files are
refreshed into the directory and the demodulized dependency source is copied into its `no-mod`, but
neither the project's `.lake` nor `no-mod/.lake` is removed, so a previously-built (e.g.
cache-restored) directory stays warm and Lake rebuilds incrementally.
-/
def prepareProject (project : System.FilePath) (toolchain : String) (demodSrc : System.FilePath) :
    IO System.FilePath := do
  let buildDir := (← buildRoot) / sanitizeToolchain toolchain / project
  IO.FS.createDirAll buildDir
  -- Refresh the project's own files (lakefile, toolchain, library sources), but never its build
  -- artifacts or a previously-generated dependency source — those are managed below / kept warm.
  copyRecursively project buildDir
    (fun f => f != ".lake" && f != "no-mod" && f != "lake-manifest.json")
  -- Refresh the path-dependency source in place, leaving any existing `no-mod/.lake` untouched.
  copyRecursively demodSrc (buildDir / "no-mod") (fun _ => true)
  pure buildDir

open Lean in
/-- Loads examples from `project`, building it under `toolchain` in its per-toolchain build dir. -/
def loadExamplesIn (project : System.FilePath) (toolchain : String) (demodSrc : System.FilePath) :
    IO (NameMap (NameMap Example)) := do
  let dir ← prepareProject project toolchain demodSrc
  loadExamples dir (overrideToolchain := some toolchain)

/-- Loads a module from `project`, building it under `toolchain` in its per-toolchain build dir. -/
def loadModuleContentIn (project : System.FilePath) (mod : String) (toolchain : String)
    (demodSrc : System.FilePath) : IO (Array ModuleItem) := do
  let dir ← prepareProject project toolchain demodSrc
  loadModuleContent dir.toString mod (overrideToolchain := some toolchain)

/--
The fixed (Lean-version-independent) demo builds. These don't depend on the toolchain under test, so
they're identical across every matrix job and are good candidates to build once and cache. Kept as
named constants so the prebuild phase and the full test run agree on the exact toolchain strings
(and hence on the build-directory names).
-/
def demoToolchain48 : String := "leanprover/lean4:v4.8.0"
@[inherit_doc demoToolchain48] def demoToolchain410 : String := "leanprover/lean4:4.10.0"

/-- The `(project, toolchain)` pairs whose builds are shared across all matrix jobs. -/
def fixedTargets : IO (List (System.FilePath × String)) := do
  pure [
    ("demo-toml", ← projectToolchain "demo-toml"),
    ("demo", ← projectToolchain "demo"),
    ("demo", demoToolchain48),
    ("demo", demoToolchain410)
  ]

/--
Runs the full test suite. `demodSrc` is the demodulized SubVerso source tree (from
`prepareDemodulizedSource`) that backs every project's `no-mod` path dependency.
-/
def fullRun (demodSrc : System.FilePath) : IO UInt32 := do
  let demoTomlTc ← projectToolchain "demo-toml"

  IO.println "Checking that the TOML project will load"
  let examplesToml ← loadExamplesIn "demo-toml" demoTomlTc demodSrc
  if examplesToml.isEmpty then
    IO.eprintln "No examples found"
    return 1
  else IO.println s!"Found {proofCount examplesToml} proofs"

  IO.println "Checking anchor test file in TOML project"
  let anchorMod := (← loadModuleContentIn "demo-toml" "Anchors" demoTomlTc demodSrc).map (·.code) |>.foldl (· ++ ·) (.empty)
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
  let examples ← loadExamplesIn "demo" (← projectToolchain "demo") demodSrc
  if examples.isEmpty then
    IO.eprintln "No examples found"
    return 1
  checkVersion "4.3.0" examples
  checkHasSorry examples
  checkIsLinted examples
  let proofCount1 := proofCount examples
  IO.println s!"Found {proofCount1} proofs "

  IO.println "Checking that the test project generates at least some deserializable JSON with 4.8.0"
  let examples' ← loadExamplesIn "demo" demoToolchain48 demodSrc
  if examples'.isEmpty then
    IO.eprintln "No examples found with later toolchain"
    return 1
  checkVersion "4.8.0" examples'
  checkHasSorry examples'
  checkIsLinted examples'
  let proofCount2 := proofCount examples'
  IO.println s!"Found {proofCount2} proofs "

  IO.println "Checking that the test project generates at least some deserializable JSON with 4.10.0"
  let examples'' ← loadExamplesIn "demo" demoToolchain410 demodSrc
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


  let oldest := ["4.0.0", "4.1.0", "4.2.0"]
  let oldest := oldest ++ oldest.map ("v" ++ ·) |>.map ("leanprover/lean4:" ++ ·)
  let myToolchain := Compat.String.trim (← IO.FS.readFile "lean-toolchain")
  if oldest.contains (Compat.String.trim myToolchain) then
    IO.println s!"Skipping induction/cases alts tests for old Lean toolchain {Compat.String.trim myToolchain}"
  else
    IO.println "Checking proof states for induction/cases alts"

    IO.println s!"Loading content from small-tests directory using Lean toolchain {myToolchain}"
    let items ← loadModuleContentIn "small-tests" "Small.TacticAlts" myToolchain demodSrc
    let content := items.map (·.code) |>.foldl (· ++ ·) (.empty)
    match content.anchored with
      | .error e =>
        IO.eprintln s!"Error loading anchored content: {e}"
        return 1
      | .ok {code:=_, anchors:=_, proofStates} =>
        let mut errors := 0
        IO.println s!"There are {proofStates.size} proof states to check"
        for (name, code, states) in desiredAltProofs do
          if let some hl := proofStates.get? name then
            let .tactics goals _ _ hl := hl
              | IO.eprintln s!"Proof state '{name}' not a proof state: {repr hl}"; errors := errors + 1
            if hl.toString != code then
              IO.eprintln s!"Proof state '{name}': expected {repr code} but got {repr hl.toString}"; errors := errors + 1
            let goalString := "\n".intercalate (goals.map (·.toString) |>.toList)
            unless states.contains goalString do
              IO.eprintln s!"Proof state '{name}': expected one of {repr states} but got {repr goalString}"; errors := errors + 1
          else
            IO.eprintln "Not found: proof state '{name}'"; errors := errors + 1
        if errors > 0 then
          IO.eprintln s!"{errors} errors encountered looking at proof states for induction/cases alts"
          return 1
    IO.println "Proof states for induction/cases alts OK"

  pure 0

/--
Builds the fixed-toolchain demo targets (or a single `<project> <toolchain>` pair) into their
per-toolchain build directories and exits, without running any assertions. Used by the CI prebuild
job to cache the builds that are shared across all matrix jobs.
-/
def prepare (demodSrc : System.FilePath) (args : List String) : IO UInt32 := do
  let targets ← match args with
    | [] => fixedTargets
    | [project, toolchain] => pure [((project : System.FilePath), toolchain)]
    | _ =>
      IO.eprintln "usage: subverso-tests prepare [<project> <toolchain>]"
      return 2
  for (project, toolchain) in targets do
    IO.println s!"Prebuilding {project} using Lean toolchain {toolchain}"
    let examples ← loadExamplesIn project toolchain demodSrc
    if examples.isEmpty then
      IO.eprintln s!"No examples found while prebuilding {project} @ {toolchain}"
      return 1
  pure 0

def main (args : List String) : IO UInt32 := do
  IO.println "Setting up demodulized SubVerso for test code"
  let demodSrc ← prepareDemodulizedSource
  match args with
  | "prepare" :: rest => prepare demodSrc rest
  | [] => fullRun demodSrc
  | _ =>
    IO.eprintln s!"Unknown arguments: {args}"
    IO.eprintln "usage: subverso-tests [prepare [<project> <toolchain>]]"
    pure 2
