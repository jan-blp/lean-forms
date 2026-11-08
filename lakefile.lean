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
require «lean-lens» from "../../lean-lens"

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

lean_lib Browser where
  roots := #[`CompiledMain]
  srcDir := "experiments/wasm"

-- Use Lake's dependency graph, without inspecting or rewriting generated C.
target browserSources pkg : FilePath := do
  let some root := pkg.findModule? `CompiledMain
    | error "Missing browser entry module"
  let imports ← (← root.transImports.fetch).await
  let jobs ← (imports.push root).mapM fun mod => mod.c.fetch
  Job.async do
    let files ← jobs.mapM fun job => job.await
    let path := pkg.buildDir / "browser-sources.txt"
    let contents := String.intercalate "\n" (files.toList.map (·.toString)) ++ "\n"
    unless (← path.pathExists) && (← IO.FS.readFile path) == contents do
      IO.FS.writeFile path contents
    return path
