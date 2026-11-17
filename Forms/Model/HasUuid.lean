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

def HasUuid.sameExceptUuid (β : Type) [HasUuid β] : Setoid β where
  r a b := ∀ uuid, setUuid uuid a = setUuid uuid b
  iseqv := {
    refl _ _ := rfl
    symm same uuid := same uuid |>.symm
    trans a b uuid := a uuid |>.trans (b uuid) }

/-- `β` with its UUID forgotten: items that differ only in their UUID are equal. At runtime it
is stored exactly as `β`. Build one with `T.mkWithoutUuid` (from `deriving instance HasUuid`),
`Item.mkWithoutUuid`, or `HasUuid.withoutUuid` on an existing item. -/
def HasUuid.WithoutUuid (β : Type) [HasUuid β] : Type :=
  Quotient (HasUuid.sameExceptUuid β)

/-- Forgets the UUID. No runtime cost since `Quotient.mk` compiles to the identity. -/
def HasUuid.withoutUuid {β : Type} [HasUuid β] : β → HasUuid.WithoutUuid β :=
  Quotient.mk _

def HasUuid.withUuid {β : Type} [HasUuid β] (uuid : Uuid) : HasUuid.WithoutUuid β → β :=
  Quotient.lift (setUuid uuid) fun _ _ same => same uuid

theorem HasUuid.id_withUuid
  {β : Type}
  [HasUuid β]
  (uuid : Uuid)
  (rest : HasUuid.WithoutUuid β)
  : HasUuid.id (HasUuid.withUuid uuid rest) = uuid := by
  induction rest using Quotient.ind with
  | _ item => exact view_set uuid item

/-- The UUID that `mkWithoutUuid` values hold before `HasUuid.withoutUuid` forgets it. -/
def Uuid.nil : Uuid := ⟨"00000000-0000-0000-0000-000000000000", by decide⟩

end Forms.Model
