module

import Forms.Runtime.Web

open Forms Forms.Runtime Forms.ExampleForms

private def usage := "Usage: forms-web [" ++ String.intercalate "|" [TypedPersonProtocol.name] ++ "] [--port PORT] [--open]"

private structure Options where
  selected : Bool := false
  port : UInt16 := 8080
  openBrowser : Bool := false

private def parseOptions
  (args : List String)
  (options : Options := {})
  : Except String Options :=
  match args with
  | [] => .ok options
  | arg :: rest =>
      if arg == "--open" then parseOptions rest { options with openBrowser := true }
      else if arg == "--port" then
        match rest with
        | [] => .error "Expected a port after --port"
        | value :: rest =>
            match value.toNat? with
            | some port =>
                if port > 0 && port ≤ 65535 then
                  parseOptions rest { options with port := port.toUInt16 }
                else .error "Port must be between 1 and 65535"
            | none => .error "Expected a port number"
      else
        if arg == TypedPersonProtocol.name && !options.selected then
          parseOptions rest { options with selected := true }
        else .error usage

private def complete (words : List String) : List String :=
  let previous := words.dropLast
  if previous.getLast? == some "--port" || previous.contains "--help" then []
  else
    match parseOptions previous with
    | .error _ => []
    | .ok options =>
        let candidates := (if !options.selected then [TypedPersonProtocol.name] else []) ++
          (if options.openBrowser then [] else ["--open"]) ++ ["--port", "--help"]
        candidates.filter (fun candidate => candidate.startsWith (words.getLast?.getD ""))

public def main (args : List String) : IO Unit := do
  if let "--complete" :: words := args then
    for candidate in complete words do IO.println candidate
    return
  if args.contains "--help" then
    IO.println usage
    return
  let options ← IO.ofExcept (parseOptions args)
  Web.run options.port options.openBrowser
