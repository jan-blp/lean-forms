module

public import Forms.Model.Format
import all Lean.Data.Json.Basic

@[expose] public section
namespace Forms.Model
open Lean

class LawfulJson (α : Type) [ToJson α] [FromJson α] : Prop where
  fromJson?_toJson : ∀ value : α, fromJson? (toJson value) = .ok value

instance : LawfulJson String := ⟨fun _ => by rfl⟩

instance : LawfulJson Bool := ⟨fun value => by cases value <;> rfl⟩

instance : LawfulJson Nat := ⟨fun _ => by rfl⟩

instance : LawfulJson Int := ⟨fun _ => by rfl⟩

instance : LawfulJson Int32 where
  fromJson?_toJson value := by
    simp [fromJson?, toJson, Json.getInt?, JsonNumber.fromInt, Int32.ofInt?_toInt]
    rfl

instance : LawfulJson Int64 := ⟨Format.int64.fromJson_toJson⟩

instance : LawfulJson Decimal := ⟨Format.decimal.fromJson_toJson⟩

instance : LawfulJson Std.Time.PlainDate := ⟨Format.date.fromJson_toJson⟩

instance : LawfulJson Uuid := ⟨Format.uuid.fromJson_toJson⟩

end Forms.Model
