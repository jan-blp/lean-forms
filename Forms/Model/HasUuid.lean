module

public import Forms.Model.Scalar
public import Forms.Model.Lens

@[expose] public section
namespace Forms.Model
open LeanLens

/-- Collection items with a unique UUID -/
class HasUuid (β : Type) where
  lens : Lens' β Uuid
  lawful : LawfulLens lens := by exact lawfulMkLens

attribute [instance] HasUuid.lawful

@[inline]
def HasUuid.id {β : Type} [HasUuid β] : β → Uuid :=
  view HasUuid.lens

@[inline]
def HasUuid.setUuid {β : Type} [HasUuid β] : Uuid → β → β :=
  set HasUuid.lens

/-- `β` with its UUID forgotten: items that differ only in their UUID are equal. At runtime it
is stored exactly as `β`. -/
def HasUuid.WithoutUuid (β : Type) [HasUuid β] : Type :=
  Quot fun first second : β => ∀ uuid, setUuid uuid first = setUuid uuid second

/-- Forgets the UUID. No runtime cost since `Quot.mk` compiles to the identity. -/
def HasUuid.withoutUuid {β : Type} [HasUuid β] : β → HasUuid.WithoutUuid β :=
  Quot.mk _

def HasUuid.withUuid {β : Type} [HasUuid β] (uuid : Uuid) : HasUuid.WithoutUuid β → β :=
  Quot.lift (setUuid uuid) fun _ _ same => same uuid

theorem HasUuid.id_withUuid
  {β : Type}
  [HasUuid β]
  (uuid : Uuid)
  (rest : HasUuid.WithoutUuid β)
  : HasUuid.id (HasUuid.withUuid uuid rest) = uuid := by
  induction rest using Quot.ind with
  | mk item => exact view_set uuid item

/-- The UUID that templates hold before `HasUuid.withoutUuid` forgets it. -/
def Uuid.nil : Uuid := ⟨"00000000-0000-0000-0000-000000000000", by decide⟩

end Forms.Model
