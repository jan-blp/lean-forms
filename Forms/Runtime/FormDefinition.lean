module

public import Forms.Runtime.ModelProtocol

@[expose] public section
namespace Forms.Runtime
open Lean

/-- A form's typed state transitions. -/
structure FormDefinition where
  State : Type
  Raw : Type
  [encode : ToJson Raw]
  /-- Decode the initial value and create the state and first snapshot. -/
  openState (value : Json) : Except String (State × ModelForm.Snapshot Raw)
  execute : State → ModelForm.Command → Except String (State × ModelForm.Snapshot Raw)

/-- A form definition and its application-specific submission endpoint. -/
structure RegisteredForm where
  definition : FormDefinition
  submitUrl : String

/-- An open form. -/
structure FormInstance where
  execute : Wire.FormRequest → Except String (FormInstance × Wire.Snapshot)

instance : Inhabited FormInstance := ⟨.mk fun _ => .error "Uninitialized form"⟩

def RegisteredForm.toWire (form : RegisteredForm) (name : String)
    (snapshot : ModelForm.Snapshot form.definition.Raw) : Wire.Snapshot :=
  letI := form.definition.encode
  snapshot.toWire name form.submitUrl

partial def RegisteredForm.instance (form : RegisteredForm) (name : String)
    (state : form.definition.State) : FormInstance :=
  .mk fun request => do
    let command ← ModelProtocol.commandFromWire request
    let (state, snapshot) ← form.definition.execute state command
    pure (form.instance name state, form.toWire name snapshot)

def RegisteredForm.open (form : RegisteredForm) (name : String) (value : Json) : Except String (FormInstance × Wire.Snapshot) := do
  let (state, snapshot) ← form.definition.openState value
  pure (form.instance name state, form.toWire name snapshot)

end Forms.Runtime
