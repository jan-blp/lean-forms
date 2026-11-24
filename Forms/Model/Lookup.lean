module

public import Forms.Model.Remote
public import Forms.Model.Report
public import Mathlib.Data.List.Nodup
import all Lean.Data.Json.Basic

@[expose] public section
namespace Forms.Model
open Lean

structure LookupKey where
  value : String
  deriving DecidableEq, BEq, Repr

instance : ToJson LookupKey where
  toJson key := .str key.value

instance : FromJson LookupKey where
  fromJson? json := do
    return { value := ← json.getStr? }

@[simp] theorem LookupKey.toJson_eq (key : LookupKey) :
    toJson key = Json.str key.value := rfl

@[simp] theorem LookupKey.fromJson_toJson (key : LookupKey) :
    fromJson? (toJson key) = .ok key := by
  cases key
  rfl

structure Reference (κ : Type) where
  id : κ
  displayText : String
  deriving DecidableEq, Repr, ToJson, FromJson

def Reference.wireKey {κ : Type} [ToJson κ] (reference : Reference κ) : LookupKey :=
  { value := (toJson reference.id).compress }

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
  keys_nodup : (found.map Reference.wireKey).Nodup

def LookupResults.empty {κ : Type} [ToJson κ] : LookupResults κ :=
  { found := [], more := false, keys_nodup := List.nodup_nil }

inductive LookupError where
  | duplicateKeys
  deriving DecidableEq, Repr

instance : ToString LookupError where
  toString
    | .duplicateKeys => "Lookup results repeat an id."

def LookupResults.ofList
  {κ : Type}
  [ToJson κ]
  (found : List (Reference κ))
  (more : Bool)
  : Except LookupError (LookupResults κ) :=
  if distinct : (found.map Reference.wireKey).Nodup then
    .ok { found, more, keys_nodup := distinct }
  else .error .duplicateKeys

def LookupResults.select
  {κ : Type}
  [ToJson κ]
  (records : List (Reference κ))
  (keep : Reference κ → Bool)
  (limit : Nat)
  : Except LookupError (LookupResults κ) := do
  let results ← LookupResults.ofList (records.filter keep) false
  return { found := results.found.take limit
           more := limit < results.found.length
           keys_nodup := List.Nodup.sublist ((List.take_sublist _ _).map _) results.keys_nodup }

instance {κ : Type} [ToJson κ] : ToJson (LookupResults κ) where
  toJson results := Json.mkObj [("found", toJson results.found), ("more", toJson results.more)]

instance {κ : Type} [ToJson κ] [FromJson κ] : FromJson (LookupResults κ) where
  fromJson? json := do
    let found : List (Reference κ) ← json.getObjValAs? _ "found"
    let more ← json.getObjValAs? Bool "more"
    (LookupResults.ofList found more).mapError toString

end Forms.Model
