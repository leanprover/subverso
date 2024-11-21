import Lake
open Lake DSL
open System (FilePath)

package «subverso» where
  precompileModules := true
  -- add package configuration options here

lean_lib SubVersoCompat where
  srcDir := "src/compat"
  roots := #[`SubVerso.Compat]

lean_lib SubVersoHighlighting where
  srcDir := "src/highlighting"
  roots := #[`SubVerso.Highlighting]

lean_lib SubVersoExamples where
  srcDir := "src/examples"
  roots := #[`SubVerso.Examples]

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


-- Compatibility shims for older Lake (where logging was manual) and
-- newer Lake (where it isn't). Necessary from Lean 4.8.0 and up.
section
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  if !env.contains `Lake.logStep then
    elabCommand <| ← `(def $(mkIdent `logStep) [Pure $(mkIdent `m)] (message : String) : $(mkIdent `m) Unit := pure ())
  if !env.contains `Lake.logInfo then
    elabCommand <| ← `(def $(mkIdent `logInfo) [Pure $(mkIdent `m)] (message : String) : $(mkIdent `m) Unit := pure ())
end

module_facet highlighted mod : FilePath := do
  let ws ← getWorkspace
  let some extract ← findLeanExe? `«subverso-extract-mod»
    | error "The subverso-extract-mod executable was not found"

  let exeJob ← extract.exe.fetch
  let modJob ← mod.olean.fetch

  let buildDir := ws.root.buildDir
  let hlFile := mod.filePath (buildDir / "highlighted") "json"

  exeJob.bindAsync fun exeFile exeTrace =>
    modJob.bindSync fun _oleanPath modTrace => do
      let depTrace := mixTrace exeTrace modTrace
      let trace ← buildFileUnlessUpToDate hlFile depTrace do
        logStep s!"Exporting highlighted source file JSON for '{mod.name}'"
        proc {
          cmd := exeFile.toString
          args := #[mod.name.toString, hlFile.toString]
          env := ← getAugmentedEnv
        }
      pure (hlFile, trace)

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
        logStep s!"Exporting highlighted example JSON for '{mod.name}'"
        proc {
          cmd := exeFile.toString
          args := #[mod.name.toString, hlFile.toString]
          env := ← getAugmentedEnv
        }
      pure (hlFile, trace)

library_facet highlighted lib : FilePath := do
  let ws ← getWorkspace
  let mods ← lib.modules.fetch
  let moduleJobs ← BuildJob.mixArray <| ← mods.mapM (fetch <| ·.facet `highlighted)
  let buildDir := ws.root.buildDir
  let hlDir := buildDir / "highlighted"
  moduleJobs.bindSync fun () trace => do
    pure (hlDir, trace)


library_facet examples lib : FilePath := do
  let ws ← getWorkspace
  let mods ← lib.modules.fetch
  let moduleJobs ← BuildJob.mixArray <| ← mods.mapM (fetch <| ·.facet `examples)
  let buildDir := ws.root.buildDir
  let hlDir := buildDir / "examples"
  moduleJobs.bindSync fun () trace => do
    pure (hlDir, trace)


package_facet highlighted pkg : FilePath := do
  let ws ← getWorkspace
  let libs := pkg.leanLibs
  let exes := pkg.leanExes.map (·.toLeanLib)
  let libJobs ← BuildJob.mixArray <| ← (libs ++ exes).mapM (fetch <| ·.facet `highlighted)
  let buildDir := ws.root.buildDir
  let hlDir := buildDir / "highlighted"
  libJobs.bindSync fun () trace => do
    logInfo s!"Highlighted code written to '{hlDir}'"
    pure (hlDir, trace)

package_facet examples pkg : FilePath := do
  let ws ← getWorkspace
  let libs := pkg.leanLibs
  let libJobs ← BuildJob.mixArray <| ← libs.mapM (fetch <| ·.facet `examples)
  let buildDir := ws.root.buildDir
  let hlDir := buildDir / "examples"
  libJobs.bindSync fun () trace => do
    logInfo s!"Highlighted code written to '{hlDir}'"
    pure (hlDir, trace)
