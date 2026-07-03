import Lake
open Lake DSL
open System (FilePath)

require subverso from "no-mod"

package «ffi» where
  precompileModules := false

target ffi.o pkg : FilePath := do
  let srcJob ← inputFile (pkg.dir / "ffi.c") true
  let picArgs := if System.Platform.isWindows then #[] else #["-fPIC"]
  buildLeanO (pkg.buildDir / "native" / "ffi.o") srcJob picArgs

target ffiShared pkg : Dynlib := do
  let oJob ← fetch <| pkg.target `ffi.o
  let libFile := pkg.sharedLibDir / nameToSharedLib "subverso_ffi_test"
  let keepSymbolArgs :=
    if System.Platform.isWindows then #[]
    else if System.Platform.isOSX then #["-Wl,-u,_lp_ffi_answer"]
    else #["-Wl,-u,lp_ffi_answer"]
  buildLeanSharedLib "subverso_ffi_test" libFile #[oJob] #[] #[] keepSymbolArgs

@[default_target]
lean_lib Ffi where
  dynlibs := #[`@/ffiShared]
