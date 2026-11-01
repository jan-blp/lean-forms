import Forms.Runtime.Web
import Forms.ExampleForms.Counter
import Forms.ExampleForms.Counters
import Forms.ExampleForms.Person
import Forms.ExampleForms.Booking

open Forms Forms.Runtime Forms.ExampleForms

private def examples := ["counter", "counters", "person", "booking"]

private def usage := "Usage: forms-web [counter|counters|person|booking] [--port PORT] [--open]"

private structure Options where
  exampleName : Option String := none
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
      else if (examples.contains arg) && options.exampleName.isNone then
        parseOptions rest { options with exampleName := some arg }
      else .error usage

private def complete (words : List String) : List String :=
  let previous := words.dropLast
  if previous.getLast? == some "--port" || previous.contains "--help" then []
  else
    match parseOptions previous with
    | .error _ => []
    | .ok options =>
        let candidates := (if options.exampleName.isNone then examples else []) ++
          (if options.openBrowser then [] else ["--open"]) ++ ["--port", "--help"]
        candidates.filter (fun candidate => candidate.startsWith (words.getLast?.getD ""))

def main (args : List String) : IO Unit := do
  if let "--complete" :: words := args then
    for candidate in complete words do IO.println candidate
    return
  if args.contains "--help" then
    IO.println usage
    return
  let options ← IO.ofExcept (parseOptions args)
  if options.exampleName == some "counters" then
    Web.run (.base Counters.state) Counters.form Counters.initial options.port options.openBrowser
  else if options.exampleName == some "person" then
    Web.run Person.personType Person.form Person.draft options.port options.openBrowser
  else if options.exampleName == some "booking" then
    Web.run Booking.bookingType Booking.form Booking.draft options.port options.openBrowser
  else
    Web.run (.base .natural) Counter.form 0 options.port options.openBrowser
