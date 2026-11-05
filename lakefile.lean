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

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

@[default_target]
lean_lib Forms

lean_lib FormTests where
  globs := #[.submodules `Tests]

@[default_target]
lean_exe tests where
  root := `Tests

target webAssets pkg : Unit := Job.async do
  unless ← (pkg.dir / "web" / "node_modules").isDir do
    error "web dependencies missing; run `npm --prefix web ci`"
  proc {
    cmd := "npm"
    args := #["--prefix", (pkg.dir / "web").toString, "run", "build", "--silent"]
  }

@[default_target]
lean_exe «forms-web» where
  root := `WebMain
  extraDepTargets := #[`webAssets]
