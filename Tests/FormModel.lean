module

public import Forms.Model.Derive
meta import Forms.Model.Path.Theorems

@[expose] public section

open Forms.Model
namespace Tests.FormModel

structure Address where
  street : String
  street_valid : street ≠ ""
  deriving FormModel

instance : ConstraintRule Address.Constraint.street_valid where
  check parts :=
    if h : parts.street ≠ "" then .valid h
    else .invalid (proof := h) (message := "Enter your delivery street.")
      (targets := locations[Address.Field.street])

structure Person where
  address : Address
  age : Nat
  subscribed : Bool
  age_valid : age ≤ 120
  delivery_valid : address.street = "Campus" → 18 ≤ age
  deriving FormModel

#fields Person.Parts

example (value : Person.Raw) :
    (locations[Person.Field.address / Address.Field.street, Person.Field.age] : Targets Person.Raw value) =
      .locations (.field Person.Field.address (.field Address.Field.street .self)) [.field Person.Field.age .self] :=
  rfl

instance : ConstraintRule Person.Constraint.age_valid where
  check parts :=
    if h : parts.age ≤ 120 then .valid h
    else .invalid (proof := h) (message := "Age must be at most 120.")
      (targets := locations[Person.Field.age])

instance : ConstraintRule Person.Constraint.delivery_valid where
  check parts :=
    if h : parts.address.street = "Campus" → 18 ≤ parts.age then .valid h
    else .invalid (proof := h) (message := "Campus delivery requires an adult.")
      (targets := locations[Person.Field.age])

inductive Delivery where
  | pickup
  | home (address : Address) (instructions : String)
  | campus (age : Nat) (adult : 18 ≤ age)
  deriving FormModel

instance : ConstraintRule Delivery.Constraint.campus_adult where
  check parts :=
    if h : 18 ≤ parts.age then .valid h
    else .invalid (proof := h) (message := "You must be an adult to receive this delivery.")
      (targets := locations[Delivery.campus.Field.age])

structure Empty where
  deriving FormModel

inductive Choice where
  | yes
  | no
  deriving FormModel

structure Line where
  amount : Nat
  amount_valid : 1 ≤ amount
  deriving FormModel

instance : ConstraintRule Line.Constraint.amount_valid where
  check parts :=
    if h : 1 ≤ parts.amount then .valid h
    else .invalid (proof := h) (message := "Enter an amount.")
      (targets := locations[Line.Field.amount])

structure Basket where
  lines : List Line
  lines_valid : 0 < lines.length
  deriving FormModel

instance : ConstraintRule Basket.Constraint.lines_valid where
  check parts :=
    if h : 0 < parts.lines.length then .valid h
    else .invalid (proof := h) (message := "Add a line.")
      (targets := locations[Basket.Field.lines])

inductive Single where
  | only (count : Nat)
  deriving FormModel

structure Pair where
  first : Address
  second : Address
  deriving FormModel

structure TwoRules where
  age : Nat
  registration : 18 ≤ age
  delivery : 18 ≤ age
  deriving FormModel

instance : ConstraintRule TwoRules.Constraint.registration where
  check parts :=
    if h : 18 ≤ parts.age then .valid h
    else .invalid (proof := h) (message := "Registration requires an adult.")
      (targets := .global)

instance : ConstraintRule TwoRules.Constraint.delivery where
  check parts :=
    if h : 18 ≤ parts.age then .valid h
    else .invalid (proof := h) (message := "Delivery requires an adult.")
      (targets := locations[TwoRules.Field.age])

structure EscapedFields where
  «first name» : String
  «match» : Nat
  «valid age» : «match» ≤ 120
  deriving FormModel

instance : ConstraintRule EscapedFields.Constraint.«valid age» where
  check parts :=
    if h : parts.«match» ≤ 120 then .valid h
    else .invalid (proof := h) (message := "Age must be at most 120.")
      (targets := locations[EscapedFields.Field.«match»])

inductive EscapedConstructor where
  | «home delivery» (parts : EscapedFields) («door code» : String)
  | «pick up»
  deriving FormModel

def check (name : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError ("FAIL " ++ name))
  IO.println ("PASS " ++ name)

def targetKeys {raw : Type} {value : raw} (error : Error value) :=
  match error.targets with
  | .global => []
  | .locations first rest => (first :: rest).map Location.keys

public def run : IO Unit := do
  let good : Person.Raw := ⟨⟨"Campus"⟩, 20, true⟩
  match Person.validate good with
  | .error _ => throw (IO.userError "Expected a valid person")
  | .ok person =>
    check "ModelValidationBuildsProofs" (person.val.age == 20 && person.val.address.street == "Campus")
    check "ModelValidationPreservesRaw" (Lean.toJson (Person.erase person.val) == Lean.toJson good)
  let invalidAge : Person.Raw := ⟨⟨"Road"⟩, 150, false⟩
  check "ModelProofFreeRawRoundTrip"
    ((Lean.fromJson? (Lean.toJson invalidAge) : Except String Person.Raw).toOption.any
      (fun decoded => Lean.toJson decoded == Lean.toJson invalidAge))
  check "ModelProofsAbsentFromJson"
    (Lean.toJson invalidAge == Lean.Json.mkObj [("address", Lean.Json.mkObj [("street", Lean.toJson "Road")]),
      ("age", Lean.toJson (150 : Nat)), ("subscribed", Lean.toJson false)])
  check "ModelInvalidAge" ((errors (Person.validate invalidAge)).map (·.message) == ["Age must be at most 120."])
  check "ModelParentConstraint" ((errors (Person.validate ⟨⟨"Campus"⟩, 16, false⟩)).map targetKeys == [[["age"]]])
  check "ModelChildFailureSkipsParent" ((errors (Person.validate ⟨⟨""⟩, 150, false⟩)).map targetKeys == [[["address", "street"]]])
  check "ModelSiblingErrorsAccumulate" ((errors (Pair.validate ⟨⟨""⟩, ⟨""⟩⟩)).map targetKeys ==
    [[["first", "street"]], [["second", "street"]]])
  check "ModelConstraintMessagesAreSpecific"
    ((errors (TwoRules.validate ⟨16⟩)).map (·.message) ==
      ["Registration requires an adult.", "Delivery requires an adult."])
  check "ModelInactiveConstructor" (Delivery.validate .pickup |>.isOk)
  check "ModelSumConstraint" ((errors (Delivery.validate (.campus ⟨16⟩))).map targetKeys == [[["campus", "age"]]])
  check "ModelSumValid" (Delivery.validate (.campus ⟨20⟩) |>.isOk)
  check "ModelSumJsonRoundTrip"
    ((Lean.fromJson? (Lean.toJson (Delivery.Raw.campus ⟨16⟩)) : Except String Delivery.Raw).toOption.any
      (fun value => Lean.toJson value == Lean.toJson (Delivery.Raw.campus ⟨16⟩)))
  check "ModelSumNestedError" ((errors (Delivery.validate (.home ⟨⟨""⟩, ""⟩))).map targetKeys == [[["home", "address", "street"]]])
  let updated := Person.Field.age.set 40 good
  check "ModelTypedFieldUpdate"
    (updated.age == 40 && updated.address.street == "Campus" && updated.subscribed)
  let street : Forms.Model.Path Person.Raw String :=
    path[Person.Field.address, Address.Field.street]
  let updated := street.set "Road" good
  check "ModelNestedPathUpdate" (street.get updated == "Road" && updated.age == 20)
  check "ModelPathLensUpdate"
    (LeanLens.view street.toLens (LeanLens.set street.toLens "Road" good) == "Road")
  check "ModelListValid" ((Basket.validate ⟨[⟨1⟩, ⟨2⟩]⟩).toOption.any (·.val.lines.length == 2))
  check "ModelListItemErrors" ((errors (Basket.validate ⟨[⟨1⟩, ⟨0⟩, ⟨0⟩]⟩)).map targetKeys ==
    [[["lines", "1", "amount"]], [["lines", "2", "amount"]]])
  check "ModelListConstraint" ((errors (Basket.validate ⟨[]⟩)).map targetKeys == [[["lines"]]])
  check "DeriveProjectActiveConstructor"
    ((Constructors.project Delivery.Constructor.campus (Delivery.Raw.campus ⟨20⟩)).map (·.age) == some 20)
  check "DeriveProjectOtherConstructor"
    (Constructors.project Delivery.Constructor.campus Delivery.Raw.pickup |>.isNone)
  check "DeriveProjectNullaryConstructor"
    (Constructors.project Delivery.Constructor.pickup Delivery.Raw.pickup |>.isSome)
  check "DeriveProjectSingleConstructor"
    ((Constructors.project Single.Constructor.only (Single.Raw.only ⟨3⟩)).map (·.count) == some 3)
  check "ModelConstructorPayloadLens"
    (Delivery.campus.Field.age.get (Delivery.campus.Field.age.set 30 ⟨20⟩) == 30)
  check "ModelTotalFieldUpdate" (Person.Field.age.get (Person.Field.age.set 40 good) == 40)
  check "ModelEmptyRecord" (Empty.validate ⟨⟩ |>.isOk)
  check "ModelNullarySum" (Choice.validate .yes |>.isOk)
  let escaped : EscapedFields.Raw := ⟨"Ada", 20⟩
  check "DeriveEscapedFieldNames"
    (EscapedFields.Field.«first name».get escaped == "Ada" &&
      EscapedFields.Field.«first name».key == "first name")
  check "DeriveEscapedConstraintName" (EscapedFields.validate escaped |>.isOk)
  check "DeriveEscapedConstraintLocation"
    ((errors (EscapedFields.validate ⟨"Ada", 150⟩)).map targetKeys == [[["match"]]])
  let delivery : EscapedConstructor.Raw := .«home delivery» ⟨escaped, "123"⟩
  check "DeriveEscapedConstructorName" (EscapedConstructor.validate delivery |>.isOk)
  check "DeriveEscapedNestedLocation"
    ((errors (EscapedConstructor.validate (.«home delivery» ⟨⟨"Ada", 150⟩, ""⟩))).map targetKeys ==
      [[["home delivery", "parts", "match"]]])
  check "DeriveEscapedJsonRoundTrip"
    ((Lean.fromJson? (Lean.toJson delivery) : Except String EscapedConstructor.Raw).toOption.any
      (fun decoded => Lean.toJson decoded == Lean.toJson delivery))

example : LeanLens.LawfulLens Person.Field.age.lens := inferInstance

example (path : Forms.Model.Path Person.Raw String) (first second : String) (raw : Person.Raw) :
    LeanLens.set path.toLens second (LeanLens.set path.toLens first raw) =
      LeanLens.set path.toLens second raw := LeanLens.set_set first second raw

example (raw : Person.Raw) (valid : Validated Person raw) : Person.erase valid.val = raw := valid.property

structure Parameterized (α : Type) where
  value : α

/-- error: FormModel requires a monomorphic type without parameters or indices -/
#guard_msgs in
deriving instance FormModel for Parameterized

inductive Indexed : Bool → Type where
  | yes : Indexed true

/-- error: FormModel requires a monomorphic type without parameters or indices -/
#guard_msgs in
deriving instance FormModel for Indexed

inductive Recursive where
  | leaf
  | next (value : Recursive)

/-- error: FormModel does not support recursive or mutually recursive types -/
#guard_msgs in
deriving instance FormModel for Recursive

structure Container where
  values : List String
  deriving FormModel

structure OptionalField where
  value : Option String

/-- error: Unsupported FormModel field type: Option String -/
#guard_msgs in
deriving instance FormModel for OptionalField

structure FunctionField where
  value : Nat → Nat

/-- error: Unsupported FormModel field type: ℕ → ℕ -/
#guard_msgs in
deriving instance FormModel for FunctionField

structure Unsupported where
  value : Int

/-- error: Field type must derive FormModel first: ℤ -/
#guard_msgs in
deriving instance FormModel for Unsupported

structure Dependent where
  size : Nat
  value : Fin size

/-- error: FormModel data fields cannot be dependent -/
#guard_msgs in
deriving instance FormModel for Dependent

structure ProofDependent where
  value : Nat
  first : value = value
  second : first = first

/-- error: FormModel proof fields cannot depend on earlier proofs -/
#guard_msgs in
deriving instance FormModel for ProofDependent

structure BinderNames where
  parts : String
  new : Nat
  valid : new ≤ 120
  deriving FormModel

private structure PrivateModel where
  value : Nat

/-- error: FormModel requires public model declarations -/
#guard_msgs in
deriving instance FormModel for PrivateModel

-- Field types must retain their meaning inside generated namespaces.
namespace TypeRoundTrip

structure Item where
  count : Nat
  deriving FormModel

abbrev Parts := Item

structure Order where
  parts : Parts
  deriving FormModel

structure Balance where
  amount : Nat
  ok : (amount : Int) - 5 ≥ 0
  deriving FormModel

example (parts : Balance.Parts) :
    Constraints.holds Balance.Constraint.ok parts ↔ (parts.amount : Int) - 5 ≥ 0 := Iff.rfl

end TypeRoundTrip

end Tests.FormModel
