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

@[default_target]
lean_lib FormsReact

lean_lib FormTests where
  globs := #[.submodules `Tests]

@[default_target]
lean_exe tests where
  root := `Tests

target webAssets pkg : Unit := do
  let jobs ← #[`Forms.Runtime.Wire, `Forms.Runtime.Web, `FormsReact.Component, `Forms.Protocol.TypeScript].mapM fun name => do
    let some mod := pkg.findModule? name | error s!"Missing protocol module {name}"
    mod.leanArts.fetch
  Job.async do
    for job in jobs do discard job.await
    unless ← (pkg.dir / "node_modules").isDir do
      error "npm dependencies missing; run `npm ci`"
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

/-- Collect the modules needed to run the form in the browser.
Unlike Lake's `transImports`, this skips `meta import` dependencies.
Excluding them avoids compiling their generated C to Wasm and saves compilation time. -/
private def runtimeModules (root : Module) : FetchM (Array Module) := do
  let mut pending := [root]
  let mut visited := Lean.NameSet.empty
  let mut modules := #[]
  while let mod :: rest := pending do
    pending := rest
    if visited.contains mod.name then continue
    visited := visited.insert mod.name
    modules := modules.push mod
    let input ← (← mod.input.fetch).await
    -- Non-`module` init functions call every import, meta ones included.
    unless input.header.isModule do
      error s!"{mod.name}: runtime import filtering requires `module`"
    for imp in input.imports do
      -- Skipped modules stay referenced by unused init functions; wasm-ld drops those.
      unless imp.isMeta do
        if let some dependency := imp.module? then
          pending := dependency :: pending
  return modules

-- Use Lake's dependency graph, without inspecting or rewriting generated C.
target browserSources pkg : FilePath := do
  let some root := pkg.findModule? `CompiledMain
    | error "Missing browser entry module"
  let modules ← runtimeModules root
  let jobs ← modules.mapM fun mod => mod.c.fetch
  Job.async do
    let files ← jobs.mapM fun job => job.await
    let path := pkg.buildDir / "browser-sources.txt"
    let contents := String.intercalate "\n" (files.toList.map (·.toString)) ++ "\n"
    if ← path.pathExists then
      if (← IO.FS.readFile path) == contents then return path
    IO.FS.createDirAll pkg.buildDir
    IO.FS.writeFile path contents
    return path
