module

public import Forms.Model.Report

@[expose] public section
namespace Forms.Model

/-- Cells of the source document that support a value, and the text they held when picked. -/
structure Evidence where
  page : Nat
  cellIds : List Nat
  text : String
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

@[reducible] instance : FormModel Evidence where
  Raw := Evidence
  erase := id

instance : Validation Evidence where
  validate value := .ok ⟨value, rfl⟩

instance : Reports Evidence where
  reports _ := []

end Forms.Model
