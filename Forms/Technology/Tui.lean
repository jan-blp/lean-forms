import Forms.Technology.Input

namespace Forms.Technology

inductive Key where
  | up
  | down
  | enter
  | escape
  | backspace
  | clear
  | quit
  | refresh
  | character (char : Char)
  deriving BEq, Repr

structure ScreenSize where
  columns : Nat
  rows : Nat
  deriving BEq

structure ScreenField where
  label : String
  value : String

structure ScreenEditor where
  label : String
  text : String
  error : Option String

structure Screen where
  fields : List ScreenField
  selected : Nat
  editor : Option ScreenEditor

class MonadTui (m : Type → Type) where
  readKey : m Key
  screenSize : m ScreenSize
  draw : Screen → m Unit

namespace Tui

structure Editor where
  text : String
  error : Option String := none

structure State (root : Ty) where
  value : Ty.denote root
  selected : Nat := 0
  editor : Option Editor := none

private def label {root : Ty} (field : FieldRef root) : String :=
  String.intercalate "." (Path.Labels.toList field.labels)

private def toggle {root type : Ty} (control : Control type) (path : Path root type) (value : Ty.denote root)
    : Ty.denote root :=
  match control with
  | .checkbox => Path.set path (!(Path.get path value)) value
  | _ => value

private def isCheckbox {type : Ty} (control : Control type) : Bool :=
  match control with
  | .checkbox => true
  | _ => false

private def shownValue {type : Ty} (control : Control type) (value : Ty.denote type) : String :=
  match control with
  | .checkbox => if value then "[x]" else "[ ]"
  | .text => value
  | .natural => toString value

/-- `none` ends the session; an unfinished edit is discarded. -/
def step {root : Ty} (form : Form root root) (state : State root) (key : Key)
    : Option (State root) :=
  if key == .quit then none else do
  let fields := Form.fieldRefs form state.value
  match state.editor with
  | some editor =>
    match key with
    | .escape => return { state with
        editor := none }
    | .clear => return { state with
        editor := some { text := "" } }
    | .backspace => return { state with
        editor := some { text := String.ofList (List.dropLast (String.toList editor.text)) } }
    | .character char => return { state with
        editor := some { text := String.push editor.text char } }
    | .enter =>
      let field ← fields[state.selected]?
      match edit field editor.text state.value with
      | .error error => return { state with
          editor := some { editor with
            error := some (InputError.message error) } }
      | .ok value => return { state with
          value := value
          selected := min state.selected (List.length (Form.fieldRefs form value) - 1)
          editor := none }
    | _ => return state
  | none =>
    match key with
    | .character 'q' | .escape => none
    | .up | .character 'k' => return { state with
        selected := state.selected - 1 }
    | .down | .character 'j' => return { state with
        selected := min (state.selected + 1) (List.length fields - 1) }
    | .enter | .character 'i' | .character ' ' =>
      match fields[state.selected]? with
      | none => return state
      | some field =>
        if isCheckbox field.control then
          let value := toggle field.control field.path state.value
          return { state with
            value := value
            selected := min state.selected (List.length (Form.fieldRefs form value) - 1) }
        else
          if key == .character ' ' then return state
          return { state with
            editor := some { text := display field.control (Path.get field.path state.value) } }
    | _ => return state

def screen {root : Ty} (form : Form root root) (state : State root) : Screen :=
  let fields := Form.fieldRefs form state.value
  let rows := List.map (fun field => {
    label := label field
    value := shownValue field.control (Path.get field.path state.value)
  }) fields
  let editor := do
    let draft ← state.editor
    let field ← fields[state.selected]?
    pure {
      label := label field
      text := draft.text
      error := draft.error
    }
  {
    fields := rows
    selected := state.selected
    editor := editor
  }

variable {m : Type → Type} [Monad m] [MonadTui m]

private partial def loop {root : Ty} [Inhabited (Ty.denote root)] (form : Form root root) (state : State root)
    (previous : Option ScreenSize) : m (Ty.denote root) := do
  let size ← MonadTui.screenSize
  if previous != some size then
    MonadTui.draw (screen form state)
  let key ← MonadTui.readKey
  if key == .refresh then
    loop form state (some size)
  else
    match step form state key with
    | none => return state.value
    | some next => loop form next none

def run {root : Ty} (form : Form root root) (value : Ty.denote root) : m (Ty.denote root) :=
  letI : Inhabited (Ty.denote root) := { default := value }
  loop form { value := value } none

end Tui
end Forms.Technology
