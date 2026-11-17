module

public import Forms.Model.Basic

@[expose] public section
namespace Forms.Model

/-- Data the server provides and the form does not edit. -/
structure ReadOnly (α : Type) where
  value : α
  deriving BEq, DecidableEq, Repr

@[reducible] instance {α : Type} : FormModel (ReadOnly α) := ⟨ReadOnly α, id⟩

instance {α : Type} : Validation (ReadOnly α) := ⟨fun value => .ok ⟨value, rfl⟩⟩

instance {α : Type} [Lean.ToJson α] : Lean.ToJson (ReadOnly α) := ⟨(Lean.toJson ·.value)⟩

instance {α : Type} [Lean.FromJson α] : Lean.FromJson (ReadOnly α) :=
  ⟨fun json => ReadOnly.mk <$> Lean.fromJson? json⟩

end Forms.Model
