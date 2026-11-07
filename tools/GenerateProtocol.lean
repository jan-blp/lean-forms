import Forms.Runtime.Wire
import Forms.Protocol.TypeScript

open Forms.Protocol Forms.Runtime.Wire

def protocol : String := "// Generated from Lean. Run npm --prefix web run generate.\n" ++
  (typescript% [Request, Success, Failure]).pretty

def main (args : List String) : IO Unit := do
  let path := "web/protocol.ts"
  if args == ["--check"] then
    unless (← IO.FS.readFile path) == protocol do
      throw (IO.userError "Generated protocol is stale; run npm --prefix web run generate")
  else
    IO.FS.writeFile path protocol
