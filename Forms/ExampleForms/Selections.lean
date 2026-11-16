module

public import Forms.Model.Component
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms
open Forms.Model

inductive Priority where
  | low
  | normal
  | high
  deriving FormModel

inductive Channel where
  | email
  | phone
  | post
  deriving FormModel

structure Preferences where
  priority : Priority
  channels : { items : List Channel // items.Nodup }
  deriving FormModel

def Preferences.form : Component [] Preferences.Raw :=
  .group "Preferences" [
    .enum path[Preferences.Field.priority] "Priority"
      [⟨.low, "Low"⟩, ⟨.normal, "Normal"⟩, ⟨.high, "High"⟩],
    .enumSet path[Preferences.Field.channels] "Channels"
      [⟨.email, "Email"⟩, ⟨.phone, "Phone"⟩, ⟨.post, "Post"⟩]]

def Preferences.initial : Preferences.Raw := ⟨.normal, ⟨[.email], by decide⟩⟩

end Forms.ExampleForms
