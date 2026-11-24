module

public import Forms.Model.Remote
public import Forms.Model.Report
public import Mathlib.Data.List.Nodup

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

structure LookupCandidate (κ payload : Type) where
  reference : Reference κ
  data : payload
  deriving DecidableEq, Repr, ToJson, FromJson

def LookupCandidate.ofReference
  {κ : Type}
  (reference : Reference κ)
  : LookupCandidate κ Unit :=
  { reference, data := () }

def LookupCandidate.wireKey
  {κ payload : Type}
  [ToJson κ]
  (candidate : LookupCandidate κ payload)
  : LookupKey :=
  candidate.reference.wireKey

inductive LookupAvailability where
  | enabled
  | disabled (reason : String)
  deriving DecidableEq, Repr

def LookupAvailability.always
  {κ payload : Type}
  (_candidate : LookupCandidate κ payload)
  : LookupAvailability :=
  .enabled

inductive LookupSelectionError where
  | unlisted (key : LookupKey)
  | disabled (key : LookupKey) (reason : String)
  deriving DecidableEq, Repr

/-- `more` when the server left some matches out. -/
structure LookupResults (κ payload : Type) [ToJson κ] where
  found : List (LookupCandidate κ payload)
  more : Bool
  keys_nodup : (found.map LookupCandidate.wireKey).Nodup

def LookupResults.empty {κ payload : Type} [ToJson κ] : LookupResults κ payload :=
  { found := [], more := false, keys_nodup := List.nodup_nil }

inductive LookupError where
  | duplicateKeys
  deriving DecidableEq, Repr

instance : ToString LookupError where
  toString
    | .duplicateKeys => "Lookup results repeat an id."

def LookupResults.ofList
  {κ payload : Type}
  [ToJson κ]
  (found : List (LookupCandidate κ payload))
  (more : Bool)
  : Except LookupError (LookupResults κ payload) :=
  if distinct : (found.map LookupCandidate.wireKey).Nodup then
    .ok { found, more, keys_nodup := distinct }
  else .error .duplicateKeys

def LookupResults.select
  {κ payload : Type}
  [ToJson κ]
  (records : List (LookupCandidate κ payload))
  (keep : LookupCandidate κ payload → Prop)
  [DecidablePred keep]
  (limit : Nat)
  : Except LookupError (LookupResults κ payload) :=
  let filtered := records.filter (fun record => decide (keep record))
  if distinct : (filtered.map LookupCandidate.wireKey).Nodup then
    .ok {
      found := filtered.take limit
      more := decide (limit < filtered.length)
      keys_nodup := List.Nodup.sublist ((List.take_sublist _ _).map _) distinct }
  else .error .duplicateKeys

def LookupResults.choose
  {κ payload : Type}
  [ToJson κ]
  (results : LookupResults κ payload)
  (availability : LookupCandidate κ payload → LookupAvailability)
  (key : LookupKey)
  : Except LookupSelectionError (Reference κ) :=
  match results.found.find? (fun candidate => decide (candidate.wireKey = key)) with
  | none => .error (.unlisted key)
  | some candidate => match availability candidate with
    | .enabled => .ok candidate.reference
    | .disabled reason => .error (.disabled key reason)

instance
  {κ payload : Type}
  [ToJson κ]
  [ToJson payload]
  : ToJson (LookupResults κ payload) where
  toJson results := Json.mkObj [("found", toJson results.found), ("more", toJson results.more)]

instance
  {κ payload : Type}
  [ToJson κ]
  [FromJson κ]
  [FromJson payload]
  : FromJson (LookupResults κ payload) where
  fromJson? json := do
    let found : List (LookupCandidate κ payload) ← json.getObjValAs? _ "found"
    let more ← json.getObjValAs? Bool "more"
    (LookupResults.ofList found more).mapError toString

end Forms.Model
