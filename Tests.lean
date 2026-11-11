import SubVerso.Highlighting
import SubVerso.Module
import SubVerso.Helper.Netstring
import Lean.Data.Json

open SubVerso.Module (ModuleItem)
open Lean.FromJson (fromJson?)
open Lean (FVarId Name)
open SubVerso.Highlighting (Highlighted)

open SubVerso

namespace SubVerso.Highlighting

partial def Highlighted.varHovers : Highlighted → Array (String × String)
  | .token ⟨.var _ type _, content⟩ => #[(content, type)]
  | .seq hls => hls.foldl (· ++ ·.varHovers) #[]
  | .span _ hl | .tactics _ _ _ hl => hl.varHovers
  | _ => #[]

partial
def Highlighted.countProofStates (hl : Highlighted) : Nat :=
  match hl with
  | .seq hls =>
    hls.map countProofStates |>.foldr (· + · ) 0
  | .span _ hl' =>
    hl'.countProofStates
  | .tactics _ _ _ hl' =>
    hl'.countProofStates + 1
  | _ => 0

/-- The severity and text of each message attached to highlighted code, in order of appearance. -/
partial
def Highlighted.messageTexts (hl : Highlighted) : Array (Highlighted.Span.Kind × String) :=
  match hl with
  | .seq hls =>
    hls.foldl (init := #[]) fun acc x => acc ++ x.messageTexts
  | .span info hl' =>
    info.map (fun (k, m) => (k, m.toString)) ++ hl'.messageTexts
  | .tactics _ _ _ hl' =>
    hl'.messageTexts
  | .point k m => #[(k, m.toString)]
  | _ => #[]

partial
def Highlighted.goals (hl : Highlighted) : Array (Highlighted.Goal Highlighted) :=
  match hl with
  | .seq hls => Id.run do
    let mut out := #[]
    for x in hls do
      out := out ++ x.goals
    out
  | .span _ hl' =>
    hl'.goals
  | .tactics goals _ _ hl' =>
    goals ++ hl'.goals
  | _ => #[]

partial
def Highlighted.tokens (hl : Highlighted) : Array Token :=
  match hl with
  | .token tok => #[tok]
  | .seq hls => Id.run do
    let mut out := #[]
    for x in hls do
      out := out ++ x.tokens
    out
  | .span _ hl' =>
    hl'.tokens
  | .tactics _ _ _ hl' =>
    hl'.tokens
  | _ => #[]

def Token.var? (tok : Token) : Option FVarId :=
  if let .var x _ _ := tok.kind then some x else none

def Highlighted.Goal.misattributedVars (goal : Highlighted.Goal Highlighted)
    (sourceVars : Array FVarId) : Array String := Id.run do
  let mut names : Array (FVarId × String) := #[]
  for h in goal.hypotheses do
    for tok in h.names do
      if let some x := tok.var? then
        names := names.push (x, tok.content)
  let mut found := #[]
  for part in #[goal.conclusion] ++ goal.hypotheses.map (·.typeAndVal) do
    for tok in part.tokens do
      if let some x := tok.var? then
        match names.find? (·.1 == x) with
        | some (_, name) =>
          if name != tok.content then found := found.push tok.content
        | none =>
          if sourceVars.contains x then found := found.push tok.content
  found

end SubVerso.Highlighting

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
    (overrideToolchain : Option String := none) (extraArgs : Array String := #[]) :
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
  let args := #["run", "--install", toolchain, "lake", "exe", "subverso-extract-mod"] ++ extraArgs ++ #[mod]
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

def desiredShadowingProofs : List (String × String) := [
  ("first", "n : Nat\nh : n = n\n⊢ ∀ (n : Nat), n = n → True"),
  ("shadowed", "n✝ : Nat\nh : n✝ = n✝\nn : Nat\nh' : n = n\n⊢ True"),
  ("binderRenamed", "x : Nat\nh : ∀ (x_1 : Nat), x_1 + x = x + x_1\n⊢ ∀ (x_1 : Nat), x_1 = x_1"),
  ("binderRenamedAgain", "x : Nat\nh : ∀ (x_2 : Nat), x_2 + x = x + x_2\nx_1 : Nat\n⊢ x_1 = x_1"),
  ("alphaEquivalent", "h₁ : ∀ (a : Nat), a = a\nh₂ : ∀ (b : Nat), b = b\n⊢ True"),
  ("hoverTypes", "α : Type\nP : α → Prop\na : α\nh : P a\n⊢ ∀ (α : Type), α = α"),
  ("hoverTypesShadowed", "α✝ : Type\nP : α✝ → Prop\na : α✝\nh : P a\nα : Type\n⊢ α = α"),
  ("constShadowed", "h : _root_.shadowingConst = 1\nshadowingConst : Nat\n⊢ shadowingConst = shadowingConst"),
  ("typeChanged", "x : Nat\nh : x = x\n⊢ x = x")
]

def desiredShadowingHovers : List (String × String × Array (String × String)) := [
  ("hoverTypes", "h", #[("P", "α → Prop"), ("a", "α")]),
  ("hoverTypesShadowed", "h", #[("P", "α✝ → Prop"), ("a", "α✝")]),
  ("typeChanged", "h", #[("x", "Nat"), ("x", "Nat")])
]

def desiredShadowingConclusionHovers : List (String × Array (String × String)) := [
  ("typeChanged", #[("x", "Nat"), ("x", "Nat")])
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

/--
Builds the `highlighted` package facet of `project` under `toolchain` in its per-toolchain build
dir, then reads the highlighted JSON that the facet wrote for `mod`.
-/
def loadHighlightedModuleIn (project : System.FilePath) (mod : String) (toolchain : String)
    (demodSrc : System.FilePath) : IO (Array ModuleItem) := do
  let dir ← prepareProject project toolchain demodSrc
  let cmd := "elan"
  let args := #["run", "--install", toolchain, "lake", "build", ":highlighted"]
  let res ← IO.Process.output {
    cmd, args, cwd := dir
    -- Unset Lake's environment variables
    env := lakeVars.map (·, none)
  }
  if res.exitCode != 0 then loadModuleContent.reportFail dir cmd args res
  let file : System.FilePath :=
    (mod.splitOn ".").foldl (· / ·) (dir / ".lake" / "build" / "highlighted") |>.withExtension "json"
  let .ok json := Lean.Json.parse (← IO.FS.readFile file)
    | throw <| IO.userError s!"Expected JSON in {file}"
  match Module.Module.fromJson? json with
  | .error err =>
    throw <| IO.userError s!"Couldn't parse JSON from {file}: {err}"
  | .ok m =>
    pure m.items

/--
Checks the anchors of the demo project's `Demo` module, given its highlighted items. The `version`
anchor reports `expectedVersion`. The `hasSorry` anchor has a warning about `sorry`. The `linted`
anchor has a linter warning. Returns the module's number of proof states.
-/
def checkDemo (items : Array ModuleItem) (expectedVersion : String) : IO Nat := do
  let code := items.map (·.code) |>.foldl (· ++ ·) .empty
  let anchors ←
    match code.anchored with
    | .error e => throw <| IO.userError s!"Error loading anchored content: {e}"
    | .ok {code := _, anchors, proofStates := _} => pure anchors
  let messagesOf (name : String) : IO (Array (Highlighting.Highlighted.Span.Kind × String)) :=
    match anchors.get? name with
    | some hl => pure hl.messageTexts
    | none => throw <| IO.userError s!"Anchor '{name}' not found"

  let infos := (← messagesOf "version").filter (·.1 == .info) |>.map (·.2)
  let version :=
    if let #[str] := infos then
      some <| Compat.String.dropRight (Compat.String.drop (Compat.String.trim str) 1) 1
    else none
  IO.println s!"Reported version {version}"
  if version != some expectedVersion then
    throw <| IO.userError s!"Unexpected version! Expected {expectedVersion}, got messages {repr infos}"

  IO.println "Making sure the `hasSorry` anchor has a sorry"
  let sorryMsgs ← messagesOf "hasSorry"
  -- Later Lean versions quote `sorry` with backticks
  let sorryTexts := ["declaration uses 'sorry'", "declaration uses `sorry`"]
  unless sorryMsgs.any (fun (k, str) => k == .warning && sorryTexts.contains (Compat.String.trim str)) do
    throw <| IO.userError s!"Expected a sorry warning, got {repr sorryMsgs}"

  IO.println "Making sure the `linted` anchor is linted"
  let lintMsgs ← messagesOf "linted"
  -- The phrasing varies a bit in Lean versions, but this is the important part
  unless lintMsgs.any (fun (k, str) => k == .warning && "unused variable `x`".isPrefixOf str) do
    throw <| IO.userError s!"Expected a linter warning, got {repr lintMsgs}"

  pure code.countProofStates

/-- Loads a module from `project`, building it under `toolchain` in its per-toolchain build dir. -/
def loadModuleContentIn (project : System.FilePath) (mod : String) (toolchain : String)
    (demodSrc : System.FilePath) (extraArgs : Array String := #[]) : IO (Array ModuleItem) := do
  let dir ← prepareProject project toolchain demodSrc
  loadModuleContent dir.toString mod (overrideToolchain := some toolchain) (extraArgs := extraArgs)

def checkTimings (project : System.FilePath) (mod : String) (toolchain : String)
    (demodSrc : System.FilePath) : IO Unit := do
  let dir ← prepareProject project toolchain demodSrc
  let cmd := "elan"
  let args := #["run", "--install", toolchain, "lake", "exe", "subverso-extract-mod", "--timings", mod]
  let res ← IO.Process.output { cmd, args, cwd := dir, env := lakeVars.map (·, none) }
  if res.exitCode != 0 then loadModuleContent.reportFail dir cmd args res
  let .ok out := Lean.Json.parse res.stdout
    | throw <| IO.userError "Expected JSON on standard output with --timings"
  if let .error err := Module.Module.fromJson? out then
    throw <| IO.userError s!"Couldn't parse module JSON with --timings: {err}"
  let lines := (res.stderr.splitOn "\n").map Compat.String.trim |>.filter (· != "")
  let some line := lines.getLast?
    | throw <| IO.userError "Expected timing JSON on standard error"
  let .ok json := Lean.Json.parse line
    | throw <| IO.userError s!"Timing output is not JSON: {line}"
  let field (j : Lean.Json) (path : List String) : IO Lean.Json :=
    path.foldlM (init := j) fun j k =>
      match j.getObjVal? k with
      | .ok v => pure v
      | .error _ => throw <| IO.userError s!"Timing JSON lacks {".".intercalate path}: {line}"
  let seconds (path : List String) : IO Float := do
    match ← field json path with
    | .num n => pure n.toFloat
    | other => throw <| IO.userError s!"Expected a number at {".".intercalate path}, got {other.compress}"
  for p in ["import", "elaboration", "highlighting", "export", "writing"] do
    discard <| seconds ["phases", p, "wallSeconds"]
    match ← field json ["phases", p, "cpuSeconds"] with
    | .num _ | .null => pure ()
    | other => throw <| IO.userError s!"Expected a number or null CPU time for {p}, got {other.compress}"
  discard <| seconds ["total", "wallSeconds"]
  let mut categoryTotal := 0.0
  for c in ["signatures", "variableTypes", "withType", "goalHypotheses", "goalTargets", "messages", "setup", "other"] do
    categoryTotal := categoryTotal + (← seconds ["highlighting", c])
  let highlightingWall ← seconds ["phases", "highlighting", "wallSeconds"]
  if (categoryTotal - highlightingWall).abs > 0.001 then
    throw <| IO.userError s!"Highlighting categories sum to {categoryTotal}, but the phase took {highlightingWall}"
  for c in ["delaboratorCalls", "runMetaMCalls"] do
    match ← field json ["counters", c] with
    | .num n =>
      if n.toFloat ≤ 0 then throw <| IO.userError s!"Expected a positive count for {c}, got {line}"
    | other => throw <| IO.userError s!"Expected a count for {c}, got {other.compress}"

/--
Reads the toolchains that the `demo` project is tested with from the file `demo-toolchains`.

The file holds one Lean version per line, as they would be written after `leanprover/lean4:` in a
`lean-toolchain` file. In the return value, each toolchain is paired with its version number.
-/
def demoToolchains : IO (List (String × String)) := do
  let versions := (← IO.FS.readFile "demo-toolchains").splitOn "\n"
    |>.map Compat.String.trim |>.filter (· != "")
  if versions.isEmpty then
    throw <| .userError "The file demo-toolchains doesn't list any Lean versions"
  pure <| versions.map fun v =>
    ("leanprover/lean4:" ++ v, if v.startsWith "v" then Compat.String.drop v 1 else v)

def toolchainVersion? (toolchain : String) : Option (Nat × Nat) :=
  let ver := (toolchain.splitOn ":").getLast!
  let ver := if ver.startsWith "v" then Compat.String.drop ver 1 else ver
  match (ver.splitOn ".").map (·.toNat?) with
  | some major :: some minor :: _ => some (major, minor)
  | _ => none

/--
The small-tests module that references a `match` auxiliary declaration by the name `toolchain`'s
compiler generates for it under asynchronous elaboration. Asynchronous elaboration is the compiler
default since the 4.19 cycle, and the generated names gained an extra suffix in the 4.21 cycle.
Version-numbered toolchains before 4.19 elaborate synchronously and get `none`. Nightlies and other
unrecognized toolchain strings are current enough for the 4.21 naming.
-/
def matchNamesModule (toolchain : String) : Option String :=
  match toolchainVersion? toolchain with
  | some (major, minor) =>
    if major > 4 || (major == 4 && minor >= 21) then some "Small.MatchNames21"
    else if major == 4 && minor >= 19 then some "Small.MatchNames19"
    else none
  | none => some "Small.MatchNames21"

def hasGeneralizedFieldNotation (toolchain : String) : Bool :=
  match toolchainVersion? toolchain with
  | some (major, minor) => major > 4 || (major == 4 && minor >= 8)
  | none => true

partial def constSignatures (name : Name) : Highlighted → Array String
  | .token ⟨.const n sig .., _⟩ => if n == name then #[sig] else #[]
  | .span _ hl | .tactics _ _ _ hl => constSignatures name hl
  | .seq hls => Id.run do
    let mut sigs := #[]
    for hl in hls do
      sigs := sigs ++ constSignatures name hl
    sigs
  | .token .. | .text .. | .point .. | .unparsed .. => #[]

def staleSignatureCases : List (Name × List String) := [
  (`fooOne, ["foo 1", "foo 1", "F[1]"]),
  (`barOne, ["bar 1", "bar 1", "⟪1⟫"]),
  (`bazOne, ["baz 1", "Z[1]", "baz 1"]),
  (`tRefl, ["(x : T)", "(x : T)", "(x : A.T)"]),
  (`uRefl, ["(x : B.U)", "(x : B.U)", "(x : U)"])
]

def staleSignatureNoDotCases : List (Name × List String) := [
  (`getEq, ["s.get", "s.get", "S.get s"])
]

def checkSignatures (mod : String) (items : Array ModuleItem) (cases : List (Name × List String)) :
    IO Nat := do
  let content := items.map (·.code) |>.foldl (· ++ ·) (.empty)
  let mut errors := 0
  for (name, expected) in cases do
    let sigs := constSignatures name content
    if sigs.size != expected.length then
      IO.eprintln s!"{mod}: expected {expected.length} occurrences of {name}, got {sigs}"
      errors := errors + 1
    else
      for (sig, part) in sigs.toList.zip expected do
        if (sig.splitOn part).length < 2 then
          IO.eprintln s!"{mod}: expected the signature of {name} to contain {repr part}, got {repr sig}"
          errors := errors + 1
  pure errors

/-- Test files that define and use code in the same module or source file -/
def inFileCodeModules (toolchain : String) : List String :=
  let ver := (toolchain.splitOn ":").getLast!
  let ver := if ver.startsWith "v" then Compat.String.drop ver 1 else ver
  let modules :=
    match (ver.splitOn ".").map (·.toNat?) with
    | some major :: some minor :: _ => major > 4 || (major == 4 && minor >= 27)
    | _ => true
  if modules then ["Small.InFileCode", "Small.InFileCodeModule"] else ["Small.InFileCode"]

def inFileCodeOutputs : List String :=
  ["42", "{ x := 1, y := 4 }", "10", "5", "in-file command", "⟪3⟫ : Nat"]

/--
The `(project, toolchain)` pairs whose builds are the same for every Lean version under test.

They are `demo-toml` under its own toolchain and `demo` under each toolchain in `demo-toolchains`.
-/
def fixedTargets : IO (List (System.FilePath × String)) := do
  let demoToml : System.FilePath × String := ("demo-toml", ← projectToolchain "demo-toml")
  pure <| demoToml :: (← demoToolchains).map fun (toolchain, _) => ("demo", toolchain)

/--
Runs the full test suite. `demodSrc` is the demodulized SubVerso source tree (from
`prepareDemodulizedSource`) that backs every project's `no-mod` path dependency.
-/
def fullRun (demodSrc : System.FilePath) : IO UInt32 := do
  let demoTomlTc ← projectToolchain "demo-toml"

  IO.println "Checking the demo module in the TOML project"
  let tomlCount ← checkDemo (← loadHighlightedModuleIn "demo-toml" "Demo" demoTomlTc demodSrc) "4.8.0"
  IO.println s!"Found {tomlCount} proofs"

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

  let mut proofCounts := #[]
  for (toolchain, version) in ← demoToolchains do
    IO.println s!"Checking the demo module with Lean toolchain {toolchain}"
    let count ← checkDemo (← loadHighlightedModuleIn "demo" "Demo" toolchain demodSrc) version
    IO.println s!"Found {count} proofs"
    proofCounts := proofCounts.push count

  if proofCounts.any (· != tomlCount) then
    IO.eprintln s!"Demo proof count mismatch: {tomlCount} in the TOML project, {proofCounts} in the demo project"
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
            IO.eprintln s!"Not found: proof state '{name}'"; errors := errors + 1
        if errors > 0 then
          IO.eprintln s!"{errors} errors encountered looking at proof states for induction/cases alts"
          return 1
    IO.println "Proof states for induction/cases alts OK"

    IO.println "Checking --timings output"
    checkTimings "small-tests" "Small.TacticAlts" myToolchain demodSrc
    IO.println "Timings output OK"

    IO.println "Checking that signatures follow mid-file changes to pretty printing"
    let items ← loadModuleContentIn "small-tests" "Small.StaleSignatures" myToolchain demodSrc
    let mut errors ← checkSignatures "Small.StaleSignatures" items staleSignatureCases
    if hasGeneralizedFieldNotation myToolchain then
      let items ← loadModuleContentIn "small-tests" "Small.StaleSignaturesNoDot" myToolchain demodSrc
      errors := errors + (← checkSignatures "Small.StaleSignaturesNoDot" items staleSignatureNoDotCases)
    if errors > 0 then
      IO.eprintln s!"{errors} errors encountered in signatures after mid-file changes"
      return 1
    IO.println "Signatures after mid-file changes OK"

  if oldest.contains myToolchain then
    IO.println s!"Skipping shadowed hypothesis, bound variable and nested format data tests for old Lean toolchain {myToolchain}"
  else
    IO.println "Checking names of shadowed hypotheses in proof states"
    let items ← loadModuleContentIn "small-tests" "Small.Shadowing" myToolchain demodSrc
    let content := items.map (·.code) |>.foldl (· ++ ·) (.empty)
    match content.anchored with
    | .error e =>
      IO.eprintln s!"Error loading anchored content: {e}"
      return 1
    | .ok {code:=_, anchors:=_, proofStates} =>
      let mut errors := 0
      for (name, expected) in desiredShadowingProofs do
        let some (.tactics goals _ _ _) := proofStates.get? name
          | IO.eprintln s!"Not found: proof state '{name}'"; errors := errors + 1
        let goalString := "\n".intercalate (goals.map (·.toString) |>.toList)
        if goalString != expected then
          IO.eprintln s!"Proof state '{name}': expected {repr expected} but got {repr goalString}"
          errors := errors + 1
      for (name, hyp, expected) in desiredShadowingHovers do
        let some (.tactics goals _ _ _) := proofStates.get? name
          | IO.eprintln s!"Not found: proof state '{name}'"; errors := errors + 1
        let mut hovers := #[]
        for g in goals do
          for h in g.hypotheses do
            if h.names.any (·.content == hyp) then
              hovers := hovers ++ h.typeAndVal.varHovers
        if hovers != expected then
          IO.eprintln s!"Proof state '{name}', hypothesis '{hyp}': expected hovers {repr expected} but got {repr hovers}"
          errors := errors + 1
      for (name, expected) in desiredShadowingConclusionHovers do
        let some (.tactics goals _ _ _) := proofStates.get? name
          | IO.eprintln s!"Not found: proof state '{name}'"; errors := errors + 1
        let mut hovers := #[]
        for g in goals do
          hovers := hovers ++ g.conclusion.varHovers
        if hovers != expected then
          IO.eprintln s!"Proof state '{name}', conclusion: expected hovers {repr expected} but got {repr hovers}"
          errors := errors + 1
      if errors > 0 then
        IO.eprintln s!"{errors} errors encountered looking at proof states with shadowed hypotheses"
        return 1
    IO.println "Names of shadowed hypotheses OK"

    IO.println "Checking variables bound in proof states"
    let items ← loadModuleContentIn "small-tests" "Small.BoundVars" myToolchain demodSrc
    let mut goals := #[]
    let mut sourceVars := #[]
    for item in items do
      goals := goals ++ item.code.goals
      sourceVars := sourceVars ++ item.code.tokens.filterMap (·.var?)
    if goals.isEmpty then
      IO.eprintln "No proof states found in Small.BoundVars"
      return 1
    let mut misattributed := #[]
    for g in goals do
      misattributed := misattributed ++ g.misattributedVars sourceVars
    unless misattributed.isEmpty do
      IO.eprintln s!"Tokens in proof states carry the variable of a different binding: {misattributed}"
      return 1
    IO.println "Variables bound in proof states OK"

    IO.println "Checking format data for nested pretty-printer output"
    let items ← loadModuleContentIn "small-tests" "Small.NestedDelab" myToolchain demodSrc (extraArgs := #["--collect-format"])
    if items.isEmpty then
      IO.eprintln "No module items found for Small.NestedDelab"
      return 1
    IO.println "Format data for nested pretty-printer output OK"

  match matchNamesModule myToolchain with
  | none =>
    IO.println s!"Skipping async auxiliary-name tests for Lean toolchain {myToolchain}"
  | some matchNamesMod =>
    IO.println "Checking auxiliary declaration names and proof states under async elaboration"
    let items ← loadModuleContentIn "small-tests" matchNamesMod myToolchain demodSrc
    if items.isEmpty then
      IO.eprintln s!"No module items found for {matchNamesMod}"
      return 1
    let content := items.map (·.code) |>.foldl (· ++ ·) (.empty)
    if content.hasError then
      IO.eprintln s!"Error span in {matchNamesMod}: the generated auxiliary name did not resolve"
      return 1
    match content.anchored with
    | .error e =>
      IO.eprintln s!"Error loading anchored content: {e}"
      return 1
    | .ok {code:=_, anchors:=_, proofStates} =>
      let some st := proofStates.get? "matchRfl"
        | IO.eprintln "Not found: proof state 'matchRfl'"; return 1
      let .tactics _ _ _ _ := st
        | IO.eprintln s!"Proof state 'matchRfl' not a proof state: {repr st}"; return 1
    IO.println "Auxiliary declaration names under async elaboration OK"

  if oldest.contains myToolchain then
    IO.println s!"Skipping in-file code tests for old Lean toolchain {myToolchain}"
  else
    for mod in inFileCodeModules myToolchain do
      IO.println s!"Checking code defined and used in {mod}"
      let items ← loadModuleContentIn "small-tests" mod myToolchain demodSrc
      let content := items.map (·.code) |>.foldl (· ++ ·) (.empty)
      if content.hasError then
        IO.eprintln s!"Error span in {mod}"
        return 1
      let infos := content.messageTexts.filter (·.1 == .info) |>.map (Compat.String.trim ·.2)
      for expected in inFileCodeOutputs do
        unless infos.contains expected do
          IO.eprintln s!"Expected the message {repr expected} in {mod}, got {repr infos}"
          return 1
      IO.println s!"Code defined and used in {mod} OK"

  pure 0

/--
Builds the fixed-toolchain demo targets (or a single `<project> <toolchain>` pair) into their
per-toolchain build directories and exits, without running any assertions. CI uses it to cache the
builds that are shared across all Lean versions under test.
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
    let items ← loadHighlightedModuleIn project "Demo" toolchain demodSrc
    if items.isEmpty then
      IO.eprintln s!"No highlighted code found while prebuilding {project} @ {toolchain}"
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
