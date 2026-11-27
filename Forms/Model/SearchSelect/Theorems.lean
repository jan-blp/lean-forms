module

public import Forms.Model.SearchSelect

public section
namespace Forms.Model
open Lean

theorem SearchChoices.options_keys
  {Key : Type}
  [ToJson Key]
  (choices : SearchChoices Key)
  : choices.options.options.map SelectOption.key
      = choices.references.map (some ∘ Reference.wireKey) := by
  simp only [options]
  split <;> simp [Function.comp_def]

theorem SearchChoices.chosen_listed
  {Key Details : Type}
  [ToJson Key]
  (results : LookupResults Key Details)
  (reference : Reference Key)
  : some reference.wireKey
      ∈ (SearchChoices.of results (some reference)).options.options.map SelectOption.key := by
  rw [options_keys]
  simp only [SearchChoices.of]
  split <;> simp_all
