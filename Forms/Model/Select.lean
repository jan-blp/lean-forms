module

public import Forms.Model.Lookup

@[expose] public section
namespace Forms.Model

structure SelectOption (Key α : Type) where
  key : Key
  label : String
  start : α

structure SelectOptions (Key α : Type) where
  options : List (SelectOption Key α)
  keys_nodup : options.map SelectOption.key |>.Nodup := by simp <;> decide
  labels_nodup : options.map SelectOption.label |>.Nodup := by simp <;> decide

inductive SelectOptionError where
  | unlisted
  | disabled (reason : String)
  deriving DecidableEq, Repr

def SelectOptions.choose
  {Key α : Type}
  [DecidableEq Key]
  (options : SelectOptions Key α)
  (availability : SelectOption Key α → OptionAvailability)
  (key : Key)
  : Except SelectOptionError (SelectOption Key α) :=
  match options.options.find? (fun option => decide (option.key = key)) with
  | none => .error .unlisted
  | some option => match availability option with
    | .enabled => .ok option
    | .disabled reason => .error (.disabled reason)

end Forms.Model
