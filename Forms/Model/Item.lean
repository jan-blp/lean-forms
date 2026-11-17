module

public import Forms.Model.Basic
public import Forms.Model.FreshId

@[expose] public section
namespace Forms.Model
open LeanLens

/-- A collection item that has no id of its own. -/
structure Item (β : Type) where
  id : Uuid
  value : β
  deriving BEq, Repr, Lean.ToJson, Lean.FromJson

inductive Item.Field (β : Type) : Type → Type where
  | id : Item.Field β Uuid
  | value : Item.Field β β

instance {β : Type} : HasUuid (Item β) where
  id := Item.id

instance {β : Type} : Fields (Item β) where
  Field := Item.Field β
  lens
    | .id => mkLens Item.id fun id item => { item with id }
    | .value => mkLens Item.value fun value item => { item with value }
  lawful
    | .id => lawfulMkLens
    | .value => lawfulMkLens
  key
    | .id => "id"
    | .value => "value"

@[reducible] instance {β : Type} [FormModel β] : FormModel (Item β) :=
  ⟨Item (Raw β), fun item => { id := item.id, value := FormModel.erase item.value }⟩

instance {β : Type} [FormModel β] [Validation β] : Validation (Item β) where
  validate raw := match Validation.validate (model := β) raw.value with
    | .ok value => .ok ⟨{ id := raw.id, value := value.val }, by simp [FormModel.erase, value.property]⟩
    | .error errors => .error (errors.map (Error.lift (value := raw) Item.Field.value))

def Item.fresh
  {m : Type → Type}
  {β : Type}
  [Monad m]
  [MonadFreshId m]
  (value : β)
  : m (Item β) := do
  return { id := ← freshId, value }

end Forms.Model
