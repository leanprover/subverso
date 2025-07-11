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
-- End compatibility infrastructure

package «subverso» where
  precompileModules := false -- temporarily disabled due to nightly-2025-03-30: true
  -- add package configuration options here

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
      modJob.mapM fun _oleanPath => do
        addPureTrace suppNS
        buildFileUnlessUpToDate' (text := true) nsFile do
          IO.FS.createDirAll (buildDir / "highlighted")
          IO.FS.writeFile nsFile suppNS
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
    let moduleJobs := Job.mixArray <$> mods.mapM (·.facet `highlighted |>.fetch)
    let buildDir := ws.root.buildDir
    let hlDir := buildDir / "highlighted"
    moduleJobs <&> fun _ => pure hlDir

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
    let moduleJobs := Job.mixArray <$> mods.mapM (·.facet `examples |>.fetch)
    let buildDir := ws.root.buildDir
    let hlDir := buildDir / "examples"
    moduleJobs <&> fun _ => pure hlDir

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
    let libJobs := (libs ++ exes).mapM fun x => x.facet `highlighted |>.fetch
    let buildDir := ws.root.buildDir
    let hlDir := buildDir / "highlighted"
    libJobs >>= fun _ => do
      Compat.logInfo s!"Highlighted code written to '{hlDir}'"
      pure (pure hlDir)

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
    let libJobs := libs.mapM (·.facet `examples |>.fetch)
    let buildDir := ws.root.buildDir
    let hlDir := buildDir / "examples"
    libJobs >>= fun _ => do
      logInfo s!"Highlighted code written to '{hlDir}'"
      pure (pure hlDir)
