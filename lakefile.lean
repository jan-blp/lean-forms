import Lake
open Lake DSL System

package «lean-forms» where
  version := v!"0.1.0"
  testDriver := "tests"
  leanOptions := #[
    { name := `autoImplicit
      value := false },
    { name := `relaxedAutoImplicit
      value := false }]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.34.1"

target terminal.o pkg : FilePath := do
  let source ← inputTextFile (pkg.dir / "native" / "terminal.c")
  let header ← inputTextFile (pkg.dir / "native" / "screen.h")
  let inputs := Job.zipWith (fun path _ => path) source header
  buildO (pkg.buildDir / "native" / "terminal.o") inputs
    #["-I", (← getLeanIncludeDir).toString] #["-std=c11", "-D_POSIX_C_SOURCE=200809L", "-fPIC"] "cc"

extern_lib terminal pkg := do
  let object ← fetch <| pkg.target ``terminal.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "terminal") #[object]

extern_lib ratatui pkg := do
  let files := #[
    pkg.dir / "native/ratatui/Cargo.toml",
    pkg.dir / "native/ratatui/Cargo.lock",
    pkg.dir / "native/ratatui/src/lib.rs"]
  let jobs ← Array.mapM (fun path => do inputTextFile path) files
  let inputs := Job.collectArray jobs
  let targetDir := pkg.dir / ".lake" / "ratatui"
  buildFileAfterDep (targetDir / "release" / nameToStaticLib "forms_ratatui") inputs fun _ => do
    proc {
      cmd := "cargo"
      args := #["build", "--release", "--locked", "--manifest-path",
        (pkg.dir / "native/ratatui/Cargo.toml").toString, "--target-dir", targetDir.toString]
      env := #[("CARGO_HOME", some (pkg.dir / ".lake" / "cargo-home").toString)]
    }

@[default_target]
lean_lib Forms

@[default_target]
lean_exe forms where
  root := `Main

@[default_target]
lean_exe tests where
  root := `Tests
