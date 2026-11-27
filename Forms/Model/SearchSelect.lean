module

public import Forms.Model.Component

@[expose] public section
namespace Forms.Model
open Lean

instance : Key LookupKey where
  encode key := "k" ++ key.value
  decode text := if text.startsWith "k" then some { value := (text.drop 1).copy } else none
  decode_encode key := by
    cases key
    simp [← String.toList_inj, String.toList_copy_drop]
  encode_ne_empty key := by simp

instance {Key : Type} [Forms.Model.Key Key] : Forms.Model.Key (Option Key) where
  encode
    | none => "n"
    | some key => "s" ++ Forms.Model.Key.encode key
  decode text :=
    if text = "n" then some none
    else if text.startsWith "s" then (Forms.Model.Key.decode (text.drop 1).copy).map some
    else none
  decode_encode key := by
    cases key with
    | none => simp
    | some key =>
      have prefixed : "s" ++ Forms.Model.Key.encode key ≠ "n" := by
        intro same
        simpa using congrArg String.toList same
      have dropped :
          (("s" ++ Forms.Model.Key.encode key).drop 1).copy = Forms.Model.Key.encode key := by
        simp [← String.toList_inj, String.toList_copy_drop]
      simp [prefixed, dropped, Forms.Model.Key.decode_encode]
  encode_ne_empty key := by
    cases key with
    | none => simp
    | some key => simp

def Reference.idText {Key : Type} [ToJson Key] (reference : Reference Key) : String :=
  let json := toJson reference.id
  match json with
  | .str text => text
  | .null
  | .bool _
  | .num _
  | .arr _
  | .obj _ => json.compress

structure SearchChoices (Key : Type) [ToJson Key] where
  references : List (Reference Key)
  keys_nodup : (references.map Reference.wireKey).Nodup

def SearchChoices.of
  {Key Details : Type}
  [ToJson Key]
  (results : LookupResults Key Details)
  (chosen : Option (Reference Key))
  : SearchChoices Key :=
  let listed : SearchChoices Key := {
    references := results.found.map (·.reference)
    keys_nodup := by
      rw [List.map_map]
      exact results.keys_nodup }
  match chosen with
  | none => listed
  | some reference =>
    let keys := listed.references.map Reference.wireKey
    have : Decidable (reference.wireKey ∈ keys) :=
      decidable_of_iff (keys.any (fun key => decide (key = reference.wireKey)) = true) (by simp)
    if shown : reference.wireKey ∈ keys then listed
    else { references := reference :: listed.references
           keys_nodup := List.nodup_cons.mpr ⟨shown, listed.keys_nodup⟩ }

def SearchChoices.label
  {Key : Type}
  [ToJson Key]
  (choices : SearchChoices Key)
  (reference : Reference Key)
  : String :=
  if 1 < (choices.references.map (·.displayText)).count reference.displayText then
    s!"{reference.displayText} ({reference.idText})"
  else reference.displayText

def SearchChoices.options
  {Key : Type}
  [ToJson Key]
  (choices : SearchChoices Key)
  : SelectOptions (Option LookupKey) (Option (Reference Key)) :=
  let option (label : Reference Key → String) (reference : Reference Key) :
      SelectOption (Option LookupKey) (Option (Reference Key)) :=
    { key := some reference.wireKey, label := label reference, start := some reference }
  have keys_nodup (label : Reference Key → String) :
      ((choices.references.map (option label)).map SelectOption.key).Nodup := by
    simpa [Function.comp_def] using choices.keys_nodup.map (Option.some_injective _)
  if labels_nodup : ((choices.references.map (option choices.label)).map SelectOption.label).Nodup
  then { options := choices.references.map (option choices.label)
         keys_nodup := keys_nodup choices.label
         labels_nodup }
  else { options := choices.references.map (option (·.wireKey.value))
         keys_nodup := keys_nodup (·.wireKey.value)
         labels_nodup := by
           have value_injective : Function.Injective LookupKey.value := by
             intro first second same
             cases first
             cases second
             simp_all
           simpa [Function.comp_def] using choices.keys_nodup.map value_injective }

def SearchChoices.availability
  {Key Details : Type}
  [ToJson Key]
  (results : LookupResults Key Details)
  (available : LookupCandidate Key Details → OptionAvailability)
  (option : SelectOption (Option LookupKey) (Option (Reference Key)))
  : OptionAvailability :=
  match results.found.find? (fun candidate => decide (some candidate.wireKey = option.key)) with
  | some candidate => available candidate
  | none => .enabled

def Component.searchSelect
  {Γ : Context}
  {α Key Details : Type}
  [ToJson Key]
  [DecidableEq Key]
  [DecidableEq Details]
  (path : Path α (Option (Reference Key)))
  (label : Computation Γ α String)
  (searchLabel : Computation Γ α String)
  (search : Computation Γ α ((searchText : String) → Source (LookupResults Key Details)))
  (availability : Computation Γ α (LookupCandidate Key Details → OptionAvailability))
  : Component Γ α :=
  let label := label.rename Renaming.shift
  let choice (results : LookupResults Key Details) : Component (⟨.writable, String⟩ :: Γ) α :=
    .selectWithAvailability path label
      { inputs := inputs[path], run := fun chosen => (SearchChoices.of results chosen).options }
      (Option.map Reference.wireKey)
      (SearchChoices.availability results <$> availability.rename Renaming.shift)
  .bind "" <|
    .sequence (.stateField .here (searchLabel.rename Renaming.shift) (.whileTyping .text)) <|
      .sequence
        (.load (search.rename Renaming.shift <*> { inputs := inputs[.ui .here], run := id }) fun
          | .ready results =>
            if results.more then
              .sequence (choice results) (.computed "" "Keep typing to narrow the list.")
            else choice results
          | .loading => .sequence (.computed "" "Loading…") (choice .empty)
          | .failed message =>
            .sequence (.computed "" s!"Could not load: {message}") (choice .empty))
        (.visibleWhen { inputs := inputs[path], run := Option.isSome }
          (.button "Clear" (Action.write path (.const none))))

end Forms.Model
