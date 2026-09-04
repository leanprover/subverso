import Lake
open Lake DSL
open System (FilePath)

require subverso from "no-mod"

package «ffi» where
  precompileModules := false

target ffi.o pkg : FilePath := do
  let srcJob ← inputFile (pkg.dir / "ffi.c") true
  let picArgs := if System.Platform.isWindows then #[] else #["-fPIC"]
  buildLeanO (pkg.buildDir / "native" / "ffi.o") srcJob picArgs #["-DLEAN_EXPORTING"]

extern_lib subversoFfiTest pkg := do
  let oJob ← fetch <| pkg.target `ffi.o
  let libFile := pkg.staticLibDir / nameToStaticLib "subverso_ffi_test"
  buildStaticLib libFile #[oJob]

@[default_target]
lean_lib Ffi where
  dynlibs := #[`@/subversoFfiTest:dynlib]
