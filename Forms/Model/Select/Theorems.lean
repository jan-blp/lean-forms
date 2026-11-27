module

public import Forms.Model.Select

public section
namespace Forms.Model

theorem SelectOptions.choose_spec
  {Key α : Type}
  [DecidableEq Key]
  {options : SelectOptions Key α}
  {availability : SelectOption Key α → OptionAvailability}
  {key : Key}
  {option : SelectOption Key α}
  (chosen : options.choose availability key = .ok option)
  : option ∈ options.options ∧ option.key = key ∧ availability option = .enabled := by
  cases found : options.options.find? (fun option => decide (option.key = key)) with
  | none => simp [choose, found] at chosen
  | some listed =>
    cases available : availability listed with
    | disabled reason => simp [choose, found, available] at chosen
    | enabled =>
      have listed_eq : listed = option := by
        simpa [choose, found, available] using chosen
      subst listed_eq
      exact ⟨List.mem_of_find?_eq_some found,
        of_decide_eq_true (List.find?_some
          (p := fun (option : SelectOption Key α) => decide (option.key = key)) found),
        available⟩

end Forms.Model
