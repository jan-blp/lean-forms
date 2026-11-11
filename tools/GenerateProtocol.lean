import Forms.Runtime.Wire
import Forms.Runtime.Web
import FormsReact.Component
import Forms.Protocol.TypeScript

open Lean Forms.Protocol Forms.Runtime.Wire Forms.Runtime.Web

/-- Server paths, keyed by route name. -/
def routesModule : String :=
  let entries := (FinEnum.toList GetRoute).map fun route => s!"  {(toJson route).compress}: {(toJson route.path).compress},\n"
  "export const routes = {\n" ++ String.join entries ++ "} as const;\n"

/-- Each output directory is replaced wholesale by its files. -/
def outputs : List (System.FilePath × List (System.FilePath × String)) := [
  ("packages/react/src/protocol",
    (typescript% [Request, Success, Failure, FormsReact.Component]).modules.map
      fun module => (module.file, module.pretty)),
  ("web/generated", [("routes.ts", routesModule)])]

def banner : String := "// Generated from Lean. Run npm --prefix web run generate.\n"

def main (args : List String) : IO Unit := do
  for (directory, files) in outputs do
    let files := files.map fun (path, content) => (directory / path, banner ++ content)
    if args == ["--check"] then
      let existing ← if ← directory.pathExists then directory.walkDir else pure #[]
      let existing ← existing.filterM fun path => return !(← path.isDir)
      let stale ← files.anyM fun (path, content) =>
        return !(← path.pathExists) || (← IO.FS.readFile path) != content
      if stale || existing.size != files.length then
        throw (IO.userError s!"Generated {directory} is stale; run npm --prefix web run generate")
    else
      if ← directory.pathExists then IO.FS.removeDirAll directory
      for (path, content) in files do
        if let some parent := path.parent then IO.FS.createDirAll parent
        IO.FS.writeFile path content
