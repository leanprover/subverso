import Lake
open Lake DSL
open System (FilePath)

-- Minimal compatibility infrastructure to make this file cross-compatible with more Lean/Lake versions
namespace Compat

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let useOldBind := mkIdent `useOldBind
  elabCommand <| ← `(def $useOldBind := !$(quote <| env.contains `Lake.buildFileUnlessUpToDate'))

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let oldMixArray := `Lake.BuildJob.mixArray
  let useOld := (env.contains oldMixArray) && !Linter.isDeprecated env oldMixArray
  let useOldMixArray := mkIdent `useOldMixArray
  elabCommand <| ← `(def $useOldMixArray := $(quote useOld))


open Lean Elab Command in
-- Compatibility shims related to hashing and tracing
#eval show CommandElabM Unit from do
  let env ← getEnv
  if env.contains `Lake.BuildTrace.ofHash then
    elabCommand <| ← `(def $(mkIdent `traceOfHash) (hash : Lake.Hash) : Lake.BuildTrace := .ofHash hash)
  else
    elabCommand <| ← `(def $(mkIdent `traceOfHash) (hash : Lake.Hash) : Lake.BuildTrace := .fromHash hash)


-- Compatibility shims for older Lake (where logging was manual) and
-- newer Lake (where it isn't). Necessary from Lean 4.8.0 and up.
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let m := mkIdent `m
  if !env.contains `Lake.logStep || Linter.isDeprecated env `Lake.logStep then
    elabCommand <| ← `(def $(mkIdent `logStep) [Pure $m] (message : String) : $m Unit := pure ())
  else
    elabCommand <| ← `(def $(mkIdent `logStep) := @Lake.logStep)
  if !env.contains `Lake.logInfo || Linter.isDeprecated env `Lake.logStep then
    elabCommand <| ← `(def $(mkIdent `logInfo) [Pure $m] (message : String) : $m Unit := pure ())
  else
    elabCommand <| ← `(def $(mkIdent `logInfo) := @Lake.logInfo)


open Lean Elab Command Term in
#eval show CommandElabM Unit from do
  let ty ← liftTermElabM do
    let e ← elabTerm (← `(fun (lib : Lake.LeanLib) => lib.modules.fetch)) none
    let t ← Meta.inferType e
    Meta.ppExpr t
  let ty := toString ty
  if ty == "LeanLib → FetchM (Job (Array Lake.Module))" then
    elabCommand <| ← `(def $(mkIdent `getMods) (lib : LeanLib) : FetchM (Array Lake.Module) := do return ← (← lib.modules.fetch).await)
  else if ty == "LeanLib → FetchM (Array Lake.Module)" then
    elabCommand <| ← `(def $(mkIdent `getMods) (lib : LeanLib) : FetchM (Array Lake.Module) := lib.modules.fetch)
  else if ty == "LeanLib → IndexBuildM (Array Lake.Module)" then
    elabCommand <| ← `(def $(mkIdent `getMods) (lib : LeanLib) : IndexBuildM (Array Lake.Module) := lib.modules.fetch)
  else throwError "Didn't recognize type of lib.modules.fetch to define compatibility shim for 'getMods': {ty}"
end Compat

def nightly? (version : String) : Option (Nat × Nat × Nat) := do
  let [_, date] := version.splitOn "-nightly-"
    | none
  let [y, m, d] := date.splitOn "-"
    | none
  return (← y.toNat?, ← m.toNat?, ← d.toNat?)

def release? (version : String) : Option (Nat × Nat × Option Nat) := do
  if let [v, rc] := version.splitOn "-rc" then
    if let [_four, major, minor] := v.splitOn "." then
      return (← major.toNat?, ← minor.toNat?, some (← rc.toNat?))
  if let [_four, major, minor] := version.splitOn "." then
    return (← major.toNat?, ← minor.toNat?, none)
  none

/--
Do precompiled modules work in the current Lean version and operating system?

Precompiled modules give a performance boost to elaboration-time code that manipulates SubVerso's
data structures, so it's useful to enable them. However, they do not work properly on macOS prior to Lean
version 4.20.

Precompilation has not been thoroughly tested on older nightly releases, so it is disabled for nightlies
prior to 2026.
-/
def supportsPrecompile (version : String) : Bool :=
  if let some (y, _m, _d) := nightly? version then
    y ≥ 2026
  else if let some (major, _minor, rc?) := release? version then
    -- lean4#6063
    !System.Platform.isOSX || (major > 20 || (major == 20 && rc?.isNone))
  else
    false

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let fieldExists := (← getEnv).contains `Lake.Package.leanOptions
  elabCommand <| ← `(def $(mkIdent `leanOptionsExists) : Bool := $(quote fieldExists))

-- End compatibility infrastructure

open Lean Elab Command in
#eval show CommandElabM Unit from do
  try
    _ ← Lean.getOptionDecl `experimental.module
    elabCommand (← `(def $(mkIdent `supportsModuleSystem) := true))
  catch
  | _ =>
    elabCommand (← `(def $(mkIdent `supportsModuleSystem) := false))

-- Old Lean doesn't have `leanOptions` field
meta if leanOptionsExists then
  package «subverso» where
    precompileModules := false -- supportsPrecompile Lean.versionString
    leanOptions := if supportsModuleSystem then #[⟨`experimental.module, true⟩] else #[]
else
  package «subverso» where
    precompileModules := false -- supportsPrecompile Lean.versionString

lean_lib SubVerso where
  srcDir := "src"
  roots := #[`SubVerso]

@[default_target]
lean_exe «subverso-tests» where
  root := `Tests
  supportInterpreter := true

@[default_target]
lean_exe «subverso-internal-tests» where
  root := `InternalTests
  supportInterpreter := true

@[default_target]
lean_exe «subverso-extract» where
  root := `Extract
  supportInterpreter := true

@[default_target]
lean_exe «subverso-extract-mod» where
  root := `ExtractModule
  supportInterpreter := true

@[default_target]
lean_exe «subverso-helper» where
  root := `Helper
  supportInterpreter := true

meta if Compat.useOldBind then
  module_facet highlighted mod : FilePath := do
    let ws ← getWorkspace
    let some extract ← findLeanExe? `«subverso-extract-mod»
      | error "The subverso-extract-mod executable was not found"

    let exeJob ← extract.exe.fetch
    let modJob ← mod.olean.fetch
    let suppNS := (← IO.getEnv "SUBVERSO_SUPPRESS_NAMESPACES").getD ""

    let buildDir := ws.root.buildDir
    let hlFile := mod.filePath (buildDir / "highlighted") "json"
    let nsFile := buildDir / "highlighted" / s!"ns-{hash suppNS}"

    exeJob.bindAsync fun exeFile exeTrace =>
      modJob.bindSync fun _oleanPath modTrace => do
        let nsTrace ← buildFileUnlessUpToDate nsFile (Compat.traceOfHash (.ofString suppNS)) do
          IO.FS.createDirAll (buildDir / "highlighted")
          IO.FS.writeFile nsFile suppNS
        let depTrace := mixTrace exeTrace (mixTrace modTrace nsTrace)
        let trace ← buildFileUnlessUpToDate hlFile depTrace do
          Compat.logStep s!"Exporting highlighted source file JSON for '{mod.name}'"
          proc {
            cmd := exeFile.toString
            args := #["--suppress-namespaces", nsFile.toString, mod.name.toString, hlFile.toString]
            env := ← getAugmentedEnv
          }
        pure (hlFile, trace)

else
  module_facet highlighted mod : FilePath := do
    let ws ← getWorkspace

    let exeJob ← «subverso-extract-mod».fetch
    let modJob ← mod.olean.fetch
    let suppNS := (← IO.getEnv "SUBVERSO_SUPPRESS_NAMESPACES").getD ""

    let buildDir := ws.root.buildDir
    let hlFile := mod.filePath (buildDir / "highlighted") "json"
    let nsFile := buildDir / "highlighted" / s!"ns-{hash suppNS}"

    exeJob.bindM fun exeFile =>
      modJob.mapM fun oleanFile => do
        addPureTrace suppNS
        buildFileUnlessUpToDate' (text := true) nsFile do
          IO.FS.createDirAll (buildDir / "highlighted")
          IO.FS.writeFile nsFile suppNS

        -- Rebuild when the SubVerso executable, the module's source, or the compiled module
        -- changes. Changes to the source code that don't change the olean must also be reflected
        -- in semantically-highlighted source, so the Lean file is important here.
        addTrace (← computeTrace exeFile)
        addTrace (← computeTrace (TextFilePath.mk mod.leanFile))
        addTrace (← computeTrace oleanFile)
        addTrace (← computeTrace (TextFilePath.mk nsFile))

        buildFileUnlessUpToDate' (text := true) hlFile <|
          proc {
            cmd := exeFile.toString
            args :=  #["--suppress-namespaces", nsFile.toString, mod.name.toString, hlFile.toString]
            env := ← getAugmentedEnv
          }
        pure hlFile

meta if Compat.useOldBind then
  module_facet examples mod : FilePath := do
    let ws ← getWorkspace
    let some extract ← findLeanExe? `«subverso-extract»
      | error "The subverso-extract executable was not found"

    let exeJob ← extract.exe.fetch
    let modJob ← mod.olean.fetch
    let suppNS := (← IO.getEnv "SUBVERSO_SUPPRESS_NAMESPACES").getD ""

    let buildDir := ws.root.buildDir
    let hlFile := mod.filePath (buildDir / "examples") "json"
    let nsFile := buildDir / "examples" / s!"ns-{hash suppNS}"

    exeJob.bindAsync fun exeFile exeTrace =>
      modJob.bindSync fun _oleanPath modTrace => do
        let depTrace := mixTrace exeTrace modTrace
        let trace ← buildFileUnlessUpToDate hlFile depTrace do
          Compat.logStep s!"Exporting highlighted example JSON for '{mod.name}'"
          proc {
            cmd := exeFile.toString
            args := #[mod.name.toString, hlFile.toString]
            env := ← getAugmentedEnv
          }
        pure (hlFile, trace)

else
  module_facet examples mod : FilePath := do
    let ws ← getWorkspace

    let exeJob ← «subverso-extract».fetch
    let modJob ← mod.olean.fetch
    let suppNS := (← IO.getEnv "SUBVERSO_SUPPRESS_NAMESPACES").getD ""

    let buildDir := ws.root.buildDir
    let hlFile := mod.filePath (buildDir / "examples") "json"
    let nsFile := buildDir / "examples" / s!"ns-{hash suppNS}"

    exeJob.bindM fun exeFile => do
      modJob.mapM fun oleanPath => do
        addPureTrace suppNS
        buildFileUnlessUpToDate' (text := true) nsFile do
          IO.FS.createDirAll (buildDir / "examples")
          IO.FS.writeFile nsFile suppNS
        addTrace (← computeTrace exeFile)
        addTrace (← computeTrace (TextFilePath.mk mod.leanFile))
        addTrace (← computeTrace oleanPath)
        Compat.logStep s!"Exporting highlighted example JSON for '{mod.name}'"
        buildFileUnlessUpToDate' (text := true) hlFile do
          proc {
            cmd := exeFile.toString
            args := #[mod.name.toString, hlFile.toString]
            env := ← getAugmentedEnv
          }
        pure hlFile

meta if Compat.useOldMixArray then
  library_facet highlighted lib : FilePath := do
    let ws ← getWorkspace
    let mods ← Compat.getMods lib
    let moduleJobs ← BuildJob.mixArray <| ← mods.mapM (fetch <| ·.facet `highlighted)
    let buildDir := ws.root.buildDir
    let hlDir := buildDir / "highlighted"
    moduleJobs.bindSync fun () trace => do
      pure (hlDir, trace)
else
  library_facet highlighted lib : FilePath := do
    let ws ← getWorkspace
    let mods ← Compat.getMods lib
    let moduleJobs ← Job.mixArray <$> mods.mapM (·.facet `highlighted |>.fetch)
    moduleJobs.mapM fun () => do
      let buildDir := ws.root.buildDir
      let hlDir := buildDir / "highlighted"
      pure hlDir

meta if Compat.useOldMixArray then
  library_facet examples lib : FilePath := do
    let ws ← getWorkspace
    let mods ← Compat.getMods lib
    let moduleJobs ← BuildJob.mixArray <| ← mods.mapM (fetch <| ·.facet `examples)
    let buildDir := ws.root.buildDir
    let hlDir := buildDir / "examples"
    moduleJobs.bindSync fun () trace => do
      pure (hlDir, trace)
else
  library_facet examples lib : FilePath := do
    let ws ← getWorkspace
    let mods ← Compat.getMods lib
    let moduleJobs ← Job.mixArray <$> mods.mapM (·.facet `examples |>.fetch)
    moduleJobs.mapM fun () => do
      let buildDir := ws.root.buildDir
      let hlDir := buildDir / "examples"
      pure hlDir

meta if Compat.useOldMixArray then
  package_facet highlighted pkg : FilePath := do
    let ws ← getWorkspace
    let libs := pkg.leanLibs
    let exes := pkg.leanExes.map (·.toLeanLib)
    let libJobs ← BuildJob.mixArray <| ← (libs ++ exes).mapM (fetch <| ·.facet `highlighted)
    let buildDir := ws.root.buildDir
    let hlDir := buildDir / "highlighted"
    libJobs.bindSync fun () trace => do
      Compat.logInfo s!"Highlighted code written to '{hlDir}'"
      pure (hlDir, trace)
else
  package_facet highlighted pkg : FilePath := do
    let ws ← getWorkspace
    let libs := pkg.leanLibs
    let exes := pkg.leanExes.map (·.toLeanLib)
    let libJobs ← Job.mixArray <$> ((libs ++ exes).mapM fun x => x.facet `highlighted |>.fetch)

    libJobs.mapM fun () => do
      let buildDir := ws.root.buildDir
      let hlDir := buildDir / "highlighted"
      Compat.logInfo s!"Highlighted code written to '{hlDir}'"
      pure hlDir

meta if Compat.useOldMixArray then
  package_facet examples pkg : FilePath := do
    let ws ← getWorkspace
    let libs := pkg.leanLibs
    let libJobs ← BuildJob.mixArray <| ← libs.mapM (fetch <| ·.facet `examples)
    let buildDir := ws.root.buildDir
    let hlDir := buildDir / "examples"
    libJobs.bindSync fun () trace => do
      Compat.logInfo s!"Highlighted code written to '{hlDir}'"
      pure (hlDir, trace)
else
  package_facet examples pkg : FilePath := do
    let ws ← getWorkspace
    let libs := pkg.leanLibs
    let libJobs ← Job.mixArray <$> libs.mapM (·.facet `examples |>.fetch)
    libJobs.mapM fun () => do
      let buildDir := ws.root.buildDir
      let hlDir := buildDir / "examples"
      logInfo s!"Highlighted code written to '{hlDir}'"
      pure hlDir

open Lean in
/-- Compute the orphaned modules in a library:
modules that appear under the glob `R.*` for some library root `R`
but are not imported by any library root.

Orphaned modules break `precompileModules` on some toolchains (lean4#14326). -/
library_facet orphanMods lib : Array Name := do
  let mods ← Compat.getMods lib
  let modNames := mods.foldl (init := NameSet.empty) (·.insert ·.name)
  let mut orphans := #[]
  for root in lib.config.roots do
    orphans ← show IO _ /- needed to catch IO.Error -/ from do
      try
        StateT.run' (s := orphans) do
          Glob.submodules root |>.forEachModuleIn lib.srcDir fun m => do
            unless modNames.contains m do
              modify (·.push m)
          get
      catch
        -- thrown by `forEachModuleIn` on roots with no corresponding directory
        | .noFileOrDirectory .. => return orphans
        | e => throw e
  return .pure orphans
