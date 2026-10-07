import Lean

namespace Forms.Runtime

/-- Parsing, help, and shell completion share these registries. -/
structure Cli (α : Type) where
  examples : List (String × (α → IO Unit))
  options : List (String × List (String × α)) := []
  initial : α

namespace Cli

private structure State (α : Type) where
  value : α
  selected : Option (String × (α → IO Unit)) := none
  pending : Option (String × List (String × α)) := none
  help : Bool := false

private def step {α : Type} (cli : Cli α) (state : State α) (word : String)
    : Except String (State α) := do
  if let some (name, values) := state.pending then
    let some entry := values.find? (fun entry => entry.1 == word)
      | throw s!"Unknown value for {name}: {word}. Choose {String.intercalate ", " (values.map Prod.fst)}"
    return { state with value := entry.2, pending := none }
  if word == "--help" then return { state with help := true }
  if let some option := cli.options.find? (fun option => option.1 == word) then
    return { state with pending := some option }
  if word.startsWith "-" then throw s!"Unknown option: {word}"
  let some entry := cli.examples.find? (fun entry => entry.1 == word)
    | throw s!"Unknown example: {word}. Choose {String.intercalate ", " (cli.examples.map Prod.fst)}"
  if state.selected.isSome then throw "Choose exactly one example"
  return { state with selected := some entry }

private def parse {α : Type} (cli : Cli α) (args : List String) : Except String (State α) :=
  args.foldlM (step cli) { value := cli.initial }

/-- The last argument is the current word, including an empty word after a space. -/
def complete {α : Type} (cli : Cli α) (words : List String) : List String :=
  match parse cli words.dropLast with
  | .error _ => []
  | .ok state =>
    let candidates := match state.pending with
      | some (_, values) => values.map Prod.fst
      | none =>
        if state.help then []
        else (if state.selected.isNone then cli.examples.map Prod.fst else []) ++
          cli.options.map Prod.fst ++ ["--help"]
    candidates.filter (fun candidate => candidate.startsWith (words.getLast?.getD ""))

private def helpText {α : Type} (cli : Cli α) : String :=
  String.intercalate "\n" (
    ["Usage: forms [example] [options]",
     "Examples: " ++ String.intercalate ", " (cli.examples.map Prod.fst),
     "Default: " ++ ((cli.examples.head?).map Prod.fst).getD "none"] ++
    cli.options.map (fun (name, values) =>
      name ++ " <value>: " ++ String.intercalate ", " (values.map Prod.fst)) ++
    ["--help: show this help"])

def run {α : Type} (cli : Cli α) (args : List String) : IO Unit := do
  if let "--complete" :: words := args then
    for candidate in cli.complete words do IO.println candidate
    return
  let state ← IO.ofExcept (parse cli args)
  if let some (name, _) := state.pending then
    throw (IO.userError s!"Expected a value after {name}")
  if state.help then
    IO.println cli.helpText
    return
  let some (_, action) := state.selected.orElse (fun _ => cli.examples.head?)
    | throw (IO.userError "No examples are registered")
  action state.value

end Cli
end Forms.Runtime
