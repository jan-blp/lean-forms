module

public import Forms.Model.Derive
public import Tests.DerivingNames.SumFirst
public import Tests.DerivingNames.SumSecond
public import Tests.DerivingNames.ExternalFirst
public import Tests.DerivingNames.ExternalSecond

@[expose] public section

open Forms.Model
namespace Tests.DerivingNames

open Lean Elab Command Meta in
elab "#reject_model " model:ident " with " expected:str : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo model
  let constants := (← getEnv).constants
  let messages := (← get).messages
  let previous := messages.reportedPlusUnreported.size
  let namespaceBefore ← getCurrNamespace
  let asyncBefore := Elab.async.get (← getOptions)
  elabCommand (← `(command| deriving instance FormModel for $model))
  let errors := ((← get).messages.reportedPlusUnreported.toList.drop previous).filter
    (·.severity matches .error)
  modify fun state => { state with messages }
  let [error] := errors | throwError "Expected one deriving error, got {errors.length}"
  let message ← error.data.toString
  unless message.startsWith s!"deriving FormModel for `{name}`:" && message.contains expected.getString do
    throwError "Unexpected deriving error: {message}"
  let leaked := (← getEnv).constants.fold (init := none) fun found declaration _ =>
    found.orElse fun _ => if constants.contains declaration then none else some declaration
  if let some declaration := leaked then
    throwError "Failed derivation left declaration `{declaration}`"
  let instance? ← liftTermElabM <| synthInstance? (mkApp (mkConst ``FormModel) (mkConst name))
  if instance?.isSome then throwError "Failed derivation left a FormModel instance"
  unless (← getCurrNamespace) == namespaceBefore && Elab.async.get (← getOptions) == asyncBefore do
    throwError "Failed derivation changed the caller's scope or options"

structure Person where
  age : Nat
  deriving FormModel

structure NestedOptional where
  value : Option (Option String)

#reject_model NestedOptional with "nested Option fields lose presence in JSON"

abbrev OptionalText := Option String

structure AliasedNestedOptional where
  value : Option OptionalText

#reject_model AliasedNestedOptional with "nested Option fields lose presence in JSON"

structure ListNestedOptional where
  values : List (Option (Option String))

#reject_model ListNestedOptional with "nested Option fields lose presence in JSON"

structure OptionalRecord where
  value : Option String
  deriving FormModel

structure WrappedOptional where
  value : Option OptionalRecord
  deriving FormModel

#guard (Lean.fromJson? (α := WrappedOptional.Raw)
    (Lean.toJson (WrappedOptional.Raw.mk (some ⟨none⟩)))).toOption.any (·.value.isSome)

example (value : Raw Person) : Person.Field.age.get (Person.Field.age.set 4 value) = 4 := rfl
example : Fields Person.Raw := Person.rawFields
example : FormModel Person := Person.formModel
example : Validation Person := Person.validation

namespace Person

example : Forms.Model.Raw Person = Raw := rfl

end Person

inductive Sum where
  | a (value : String)
  | b
  deriving FormModel

example : Constructors Sum.Raw := Sum.constructors
example : LawfulConstructors Sum.Raw := Sum.lawfulConstructors
#guard reprStr (Constructors.tag (α := Sum.Raw) (.a ⟨""⟩)) == "Tests.DerivingNames.Sum.Tag.a"

example : FormModel Models.ExternalFirst := Models.ExternalFirst.formModel
example : FormModel Models.ExternalSecond := Models.ExternalSecond.formModel
example : Constructors Shared.SumFirst.Raw := Shared.SumFirst.constructors
example : Constructors Shared.SumSecond.Raw := Shared.SumSecond.constructors

inductive HelperNames where
  | tag
  | inject
  | project
  deriving FormModel

structure Form where
  value : String
  deriving FormModel

namespace Signup

structure Form where
  value : String
  deriving FormModel

end Signup

structure KeyField where
  key : String

#reject_model KeyField with "KeyField.Field.key"

structure LensField where
  lens : Nat

#reject_model LensField with "LensField.Field.lens"

structure ConversionField where
  toRaw : String

#reject_model ConversionField with "ConversionField.Parts.toRaw"

structure InstanceField where
  formModel : String

#reject_model InstanceField with "InstanceField.formModel"

inductive RawConstructor where
  | Raw

#reject_model RawConstructor with "RawConstructor.Raw"

structure ProofField where
  value : String
  holds : True

#reject_model ProofField with "ProofField.Constraint.holds"

inductive ConstraintNames where
  | a_b (c : True)
  | a (b_c : True)

#reject_model ConstraintNames with "ConstraintNames.Constraint.a_b_c"

structure Occupied where
  value : String

def Occupied.Raw := Nat

#reject_model Occupied with "Occupied.Raw"

structure PrivateOccupied where
  value : String

private def PrivateOccupied.Raw := Nat

#reject_model PrivateOccupied with "private declaration"

inductive PrivateSum where
  | a (value : String)
  | b

private def PrivateSum.Raw := Nat

#reject_model PrivateSum with "private declaration"

inductive CasesOnField where
  | c (casesOn : Nat)
  | d

set_option Elab.async true in
#reject_model CasesOnField with "constructor `Tests.DerivingNames.CasesOnField.c`"

inductive RecField where
  | c (rec : Nat)
  | d

#reject_model RecField with "RecField.c.Raw.rec"

inductive CtorIdxField where
  | c (ctorIdx : Nat)
  | d

#reject_model CtorIdxField with "CtorIdxField.c.Raw.ctorIdx"

inductive CtorElimField where
  | c (ctorElim : Nat) (other : Nat)
  | d

#reject_model CtorElimField with "CtorElimField.c.Field.ctorElim"

inductive OfNatConstructor where
  | ofNat
  | other

#reject_model OfNatConstructor with "OfNatConstructor.Raw.ofNat"

structure NeedsRule where
  value : Nat
  valid : True
  deriving FormModel

example : Constraints NeedsRule.Constraint := NeedsRule.constraints

structure Retry where
  child : NeedsRule

#reject_model Retry with "Validation NeedsRule is missing"

instance : ConstraintRule NeedsRule.Constraint.valid := ⟨fun _ => .valid trivial⟩

deriving instance FormModel for Retry

example : Validation Retry := Retry.validation

structure Extension where
  value : String

def Extension.Raw.custom : Nat := 1

deriving instance FormModel for Extension

end Tests.DerivingNames
