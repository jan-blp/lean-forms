module

public import Forms.Model.Remote
public import Forms.Model.Report
public import Mathlib.Data.List.Nodup
public import Batteries.Data.List.Pairwise

@[expose] public section
namespace Forms.Model
open Lean

structure Reference (κ : Type) where
  id : κ
  label : String
  deriving DecidableEq, Repr, ToJson, FromJson

/-- Names the reference on the wire. -/
def Reference.key {κ : Type} [ToJson κ] (reference : Reference κ) : String :=
  (toJson reference.id).compress

@[reducible] instance {κ : Type} : FormModel (Reference κ) where
  Raw := Reference κ
  erase := id

instance {κ : Type} : Validation (Reference κ) where
  validate value := .ok ⟨value, rfl⟩

instance {κ : Type} : Reports (Reference κ) where
  reports _ := []

/-- `more` when the server left some matches out. -/
structure LookupResults (κ : Type) [ToJson κ] where
  found : List (Reference κ)
  more : Bool
  keys_nodup : (found.map Reference.key).Nodup

def LookupResults.empty {κ : Type} [ToJson κ] : LookupResults κ :=
  { found := [], more := false, keys_nodup := List.nodup_nil }

/-- Drops repeated ids. -/
def LookupResults.select
  {κ : Type}
  [ToJson κ]
  (records : List (Reference κ))
  (keep : Reference κ → Bool)
  (limit : Nat)
  : LookupResults κ :=
  let distinct := (records.filter keep).pwFilter (·.key ≠ ·.key)
  { found := distinct.take limit
    more := limit < distinct.length
    keys_nodup := List.Nodup.sublist ((List.take_sublist _ _).map _)
      (List.pairwise_map.mpr (List.pairwise_pwFilter _)) }

instance {κ : Type} [ToJson κ] : ToJson (LookupResults κ) where
  toJson results := Json.mkObj [("found", toJson results.found), ("more", toJson results.more)]

instance {κ : Type} [ToJson κ] [FromJson κ] : FromJson (LookupResults κ) where
  fromJson? json := do
    let found : List (Reference κ) ← json.getObjValAs? _ "found"
    let more ← json.getObjValAs? Bool "more"
    if distinct : (found.map Reference.key).Nodup then
      return { found, more, keys_nodup := distinct }
    throw "Lookup results repeat an id."

end Forms.Model
