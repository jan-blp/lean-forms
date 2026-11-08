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

require batteries from git "https://github.com/jan-blp/batteries" @ "v4.35.0-wasm.1"
require mathlib from git "https://github.com/jan-blp/mathlib4" @ "v4.35.0-wasm.1"
require «lean-lens» from git "https://github.com/janmasrovira/lean-lens" @ "816a71f8264c700c200d01149ac43e96ae5d694a"

@[default_target]
lean_lib Forms

lean_lib FormTests where
  globs := #[.submodules `Tests]

@[default_target]
lean_exe tests where
  root := `Tests

target webAssets pkg : Unit := do
  let jobs ← #[`Forms.Runtime.Wire, `Forms.Protocol.TypeScript].mapM fun name => do
    let some mod := pkg.findModule? name | error s!"Missing protocol module {name}"
    mod.leanArts.fetch
  Job.async do
    for job in jobs do discard job.await
    unless ← (pkg.dir / "web" / "node_modules").isDir do
      error "web dependencies missing; run `npm --prefix web ci`"
    proc {
      cmd := "npm"
      args := #["--prefix", (pkg.dir / "web").toString, "run", "build:prepared", "--silent"]
    }

@[default_target]
lean_exe «forms-web» where
  root := `WebMain
  extraDepTargets := #[`webAssets]

lean_lib Browser where
  roots := #[`CompiledMain]
  srcDir := "wasm"

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
    if ← path.pathExists then
      if (← IO.FS.readFile path) == contents then return path
    IO.FS.createDirAll pkg.buildDir
    IO.FS.writeFile path contents
    return path
