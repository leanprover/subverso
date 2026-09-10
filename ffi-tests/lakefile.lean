import Lake
open Lake DSL
open System (FilePath)

require subverso from "no-mod"

package «ffi»

target ffi.o pkg : FilePath := do
  let src ← inputFile (pkg.dir / "ffi.c") true
  buildLeanO (pkg.buildDir / "native" / "ffi.o") src #[] #["-DLEAN_EXPORTING"]

target ffiShared pkg : Dynlib := do
  let obj ← ffi.o.fetch
  let name := "subverso_ffi_test"
  buildLeanSharedLib name (pkg.sharedLibDir / nameToSharedLib name) #[obj] #[]

-- A separate library lets importers load the bindings and C object together.
lean_lib FfiBindings where
  roots := #[`Ffi.Bindings]
  precompileModules := true
  moreLinkObjs := #[ffi.o]

-- Here the C implementation remains in its own shared library, which Lake must load as well.
lean_lib FfiSharedBindings where
  roots := #[`Ffi.SharedBindings]
  precompileModules := true
  moreLinkLibs := #[ffiShared]

@[default_target]
lean_lib Ffi where
  -- Separate test modules keep the two native-library loading paths independent.
  roots := #[`FfiTest, `FfiSharedTest]
