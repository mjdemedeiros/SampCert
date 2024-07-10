import Lake
open Lake DSL
open System IO FS

package «sampcert» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.9.0"

@[default_target]
lean_lib «SampCert» where

lean_lib «FastExtract» where

lean_lib «VMC» where

lean_exe SampCertBin where
  root := `SampCert

target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "ffi.o"
  let srcJob ← inputFile <| pkg.dir / "ffi.cpp"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "c++" getLeanTrace

extern_lib libleanffi pkg := do
  let ffiO ← ffi.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.nativeLibDir / name) #[ffiO]



-- From doc-gen4
meta if get_config? env = some "doc" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
