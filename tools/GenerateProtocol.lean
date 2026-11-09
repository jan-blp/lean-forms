import Forms.Runtime.Wire
import FormsReact.Component
import Forms.Protocol.TypeScript

open Forms.Protocol Forms.Runtime.Wire

def directory : System.FilePath := "packages/react/src/protocol"

def files : List (System.FilePath × String) :=
  (typescript% [Request, Success, Failure, FormsReact.Component]).modules.map fun module =>
    (directory / module.file,
      "// Generated from Lean. Run npm --prefix web run generate.\n" ++ module.pretty)

def main (args : List String) : IO Unit := do
  if args == ["--check"] then
    let existing ← if ← directory.pathExists then directory.walkDir else pure #[]
    let existing ← existing.filterM fun path => return !(← path.isDir)
    let stale ← files.anyM fun (path, content) => return !(← path.pathExists) || (← IO.FS.readFile path) != content
    if stale || existing.size != files.length then
      throw (IO.userError "Generated protocol is stale; run npm --prefix web run generate")
  else
    if ← directory.pathExists then IO.FS.removeDirAll directory
    for (path, content) in files do
      if let some parent := path.parent then IO.FS.createDirAll parent
      IO.FS.writeFile path content
