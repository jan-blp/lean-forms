import Forms.ExampleForms.Thermostat

namespace Forms.Presentation.OldRefinements

structure ErrorLocation (root : DataType) where
  {t : DataType}
  path : Path root t

structure Constraint (root : DataType) where
  condition : Expr root .boolean
  errorMessage : String
  locations : List (ErrorLocation root)

inductive RefinedDataType : (unrefined : DataType) → Type 1 where
  | base (t : DataType) : RefinedDataType t
  | refine {t : DataType}
      (refined : RefinedDataType t)
      (constraint : Constraint t)
      : RefinedDataType t
  | sum {tags : Enum} {constructors : tags → DataType}
      (branches : (i : tags) → RefinedDataType (constructors i)) : RefinedDataType (.sum tags constructors)
  | list {element : DataType}
      (item : RefinedDataType element)
      : RefinedDataType (.list element)
  | record {fieldNames : Enum} {fieldTypes : fieldNames → DataType}
      (refinements : (i : fieldNames) → RefinedDataType (fieldTypes i))
      : RefinedDataType (.record fieldNames fieldTypes)

structure RefinedDataType.Denotation (t : DataType) where
  ValidatedValue : Type
  erase : ValidatedValue → ⟦t⟧

namespace RefinedDataType

@[reducible] def denotation {t : DataType} (r : RefinedDataType t) : Denotation t :=
  match r with
  | .base t => ⟨⟦t⟧, id⟩
  | .refine refined constraint =>
      let inner := denotation refined
      { ValidatedValue := { value : inner.ValidatedValue //
          constraint.condition.eval (inner.erase value) = true }
        erase := fun value => inner.erase value.val }
  | .record fields =>
      { ValidatedValue := (i : _) → (denotation (fields i)).ValidatedValue
        erase := fun value i => (denotation (fields i)).erase (value i) }
  | .list item =>
      { ValidatedValue := List (denotation item).ValidatedValue
        erase := List.map (denotation item).erase }
  | .sum branches =>
      { ValidatedValue := SumValue (fun i => (denotation (branches i)).ValidatedValue)
        erase := fun value =>
          { tag := value.tag, payload := (denotation (branches value.tag)).erase value.payload } }

abbrev ValidatedValue {t : DataType} (r : RefinedDataType t) :=
  r.denotation.ValidatedValue

def erase {t : DataType} (r : RefinedDataType t) : r.ValidatedValue → ⟦t⟧ :=
  r.denotation.erase

def validate {t : DataType} (r : RefinedDataType t) (value : ⟦t⟧) : Option r.ValidatedValue :=
  match r with
  | .base _ => some value
  | .refine inner constraint => do
      let validated ← inner.validate value
      if h : constraint.condition.eval (inner.erase validated) = true then
        return ⟨validated, h⟩
      else none
  | .record fields => Forms.sequence (fun i => (fields i).validate (value i))
  | .list item => value.mapM item.validate
  | .sum branches =>
      Option.map (fun validated => { tag := value.tag, payload := validated })
        ((branches value.tag).validate value.payload)

end RefinedDataType

def atLeastFive : Expr .natural .boolean :=
  .natLe (.value 5) (.project .self)

def atLeastFiveType : RefinedDataType .natural :=
  .refine (.base .natural)
    { condition := atLeastFive
      errorMessage := "Must be at least 5."
      locations := [⟨.self⟩] }

structure TemperatureWithLowerBound where
  val : Nat
  isValid : atLeastFive.eval val = true

def lowerBoundDenotation : RefinedDataType.Denotation .natural where
  ValidatedValue := TemperatureWithLowerBound
  erase := fun value => value.val

-- The lower-bound refinement stores exactly this evidence.
example (value : atLeastFiveType.ValidatedValue) :
    atLeastFive.eval value.val = true := value.property

def atMostThirty : Expr .natural .boolean :=
  .natLe (.project .self) (.value 30)

def temperatureType : RefinedDataType .natural :=
  .refine atLeastFiveType
    { condition := atMostThirty
      errorMessage := "Must be at most 30."
      locations := [⟨.self⟩] }

def homeSetting : temperatureType.ValidatedValue :=
  ⟨⟨18, by decide⟩, by decide⟩

def awaySetting : temperatureType.ValidatedValue :=
  ⟨⟨16, by decide⟩, by decide⟩

#guard temperatureType.erase homeSetting == 18
#guard (temperatureType.validate 4).isNone
#guard (temperatureType.validate 5).isSome
#guard (temperatureType.validate 30).isSome
#guard (temperatureType.validate 31).isNone

open ExampleForms.Thermostat

def awayNotWarmer : Expr thermostat .boolean :=
  .natLe (.project awayTemperature) (.project homeTemperature)

def awayConstraint : Constraint thermostat where
  condition := awayNotWarmer
  errorMessage := "Away must not exceed Home."
  locations := [⟨awayTemperature⟩]

def thermostatFields : RefinedDataType thermostat :=
  .record fun _ => temperatureType

def thermostatRule : RefinedDataType thermostat :=
  .refine thermostatFields awayConstraint

def correctedTemperatures : ⟦thermostat⟧ := fun
  | .home => 18
  | .away => 16

def validatedFields : thermostatFields.ValidatedValue := fun
  | .home => homeSetting
  | .away => awaySetting

def acceptedThermostat : thermostatRule.ValidatedValue :=
  ⟨validatedFields, by decide⟩

#guard thermostatRule.erase acceptedThermostat .home == 18
#guard thermostatRule.erase acceptedThermostat .away == 16

-- The proposition tree lists the evidence carried at the different layers.
example (setting : thermostatRule.ValidatedValue) :
    let value := thermostatRule.erase setting
    ((5 ≤ value .home ∧ value .home ≤ 30) ∧
     (5 ≤ value .away ∧ value .away ≤ 30)) ∧ value .away ≤ value .home := by
  exact ⟨⟨⟨of_decide_eq_true (setting.val .home).val.property,
              of_decide_eq_true (setting.val .home).property⟩,
           ⟨of_decide_eq_true (setting.val .away).val.property,
              of_decide_eq_true (setting.val .away).property⟩⟩,
         of_decide_eq_true setting.property⟩

#guard (thermostatRule.validate correctedTemperatures).isSome
#guard (thermostatRule.validate (fun | .home => 18 | .away => 22)).isNone
#guard (thermostatRule.validate (fun | .home => 18 | .away => 4)).isNone

end Forms.Presentation.OldRefinements
