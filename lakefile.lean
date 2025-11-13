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
Are precompiled modules known to work with this version and SubVerso?

Precompiled modules give a performance boost to elaboration-time code that manipulates SubVerso's
data structures, but they work differently across Lean versions.

Precompiled modules may work with more versions; the versions checked here are those releases that
have been specifically checked together with nightly releases that are considered probable (and
implicitly checked by downstream projects).
-/
def supportsPrecompile (version : String) : Bool :=
  if let some (y, m, _d) := nightly? version then
    y ≥ 2025 && m ≥ 6
  else
    version ∈ [
      "4.21.0",
      "4.22.0-rc4"
    ]

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
  srcDir := "src/"
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
    let some extract ← findLeanExe? `«subverso-extract-mod»
      | error "The subverso-extract-mod executable was not found"

    let exeJob ← extract.exe.fetch
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

        -- Rebuild if either the SubVerso executable changes, or if the module changes
        addTrace (← fetchFileTrace exeFile)
        addTrace (← fetchFileTrace oleanFile)

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

    let buildDir := ws.root.buildDir
    let hlFile := mod.filePath (buildDir / "examples") "json"

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
    let some extract ← findLeanExe? `«subverso-extract»
      | error "The subverso-extract executable was not found"

    let exeJob ← extract.exe.fetch
    let modJob ← mod.olean.fetch

    let buildDir := ws.root.buildDir
    let hlFile := mod.filePath (buildDir / "examples") "json"

    exeJob.bindM fun exeFile =>
      modJob.mapM fun _oleanPath => do
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
