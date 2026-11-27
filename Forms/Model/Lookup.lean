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

structure Reference (Key : Type) where
  id : Key
  displayText : String
  deriving DecidableEq, Repr, ToJson, FromJson

def Reference.wireKey {Key : Type} [ToJson Key] (reference : Reference Key) : LookupKey :=
  { value := (toJson reference.id).compress }

@[reducible] instance {Key : Type} : FormModel (Reference Key) where
  Raw := Reference Key
  erase := id

instance {Key : Type} : Validation (Reference Key) where
  validate value := .ok ⟨value, rfl⟩

instance {Key : Type} : Reports (Reference Key) where
  reports _ := []

structure LookupCandidate (Key Details : Type) where
  reference : Reference Key
  /-- Details from the lookup response, used for filtering and availability checks.
  For example, a business partner's VAT number for searching and blocked status for availability. -/
  details : Details
  deriving DecidableEq, Repr, ToJson, FromJson

def LookupCandidate.ofReference
  {Key : Type}
  (reference : Reference Key)
  : LookupCandidate Key Unit :=
  { reference, details := () }

def LookupCandidate.wireKey
  {Key Details : Type}
  [ToJson Key]
  (candidate : LookupCandidate Key Details)
  : LookupKey :=
  candidate.reference.wireKey

inductive OptionAvailability where
  | enabled
  | disabled (reason : String)
  deriving DecidableEq, Repr

def OptionAvailability.always {α : Type} (_option : α) : OptionAvailability :=
  .enabled

inductive LookupSelectionError where
  | unlisted (key : LookupKey)
  | disabled (key : LookupKey) (reason : String)
  deriving DecidableEq, Repr

/-- `more` when the server left some matches out. -/
structure LookupResults (Key Details : Type) [ToJson Key] where
  found : List (LookupCandidate Key Details)
  more : Bool
  keys_nodup : (found.map LookupCandidate.wireKey).Nodup

def LookupResults.empty {Key Details : Type} [ToJson Key] : LookupResults Key Details :=
  { found := [], more := false, keys_nodup := List.nodup_nil }

inductive LookupError where
  | duplicateKeys
  deriving DecidableEq, Repr

instance : ToString LookupError where
  toString
    | .duplicateKeys => "Lookup results repeat an id."

def LookupResults.ofList
  {Key Details : Type}
  [ToJson Key]
  (found : List (LookupCandidate Key Details))
  (more : Bool)
  : Except LookupError (LookupResults Key Details) :=
  if distinct : (found.map LookupCandidate.wireKey).Nodup then
    .ok { found, more, keys_nodup := distinct }
  else .error .duplicateKeys

def LookupResults.select
  {Key Details : Type}
  [ToJson Key]
  (records : List (LookupCandidate Key Details))
  (keep : LookupCandidate Key Details → Prop)
  [DecidablePred keep]
  (limit : Nat)
  : Except LookupError (LookupResults Key Details) :=
  let filtered := records.filter (fun record => decide (keep record))
  if distinct : (filtered.map LookupCandidate.wireKey).Nodup then
    .ok {
      found := filtered.take limit
      more := decide (limit < filtered.length)
      keys_nodup := List.Nodup.sublist ((List.take_sublist _ _).map _) distinct }
  else .error .duplicateKeys

def LookupResults.choose
  {Key Details : Type}
  [ToJson Key]
  (results : LookupResults Key Details)
  (availability : LookupCandidate Key Details → OptionAvailability)
  (key : LookupKey)
  : Except LookupSelectionError (Reference Key) :=
  match results.found.find? (fun candidate => decide (candidate.wireKey = key)) with
  | none => .error (.unlisted key)
  | some candidate => match availability candidate with
    | .enabled => .ok candidate.reference
    | .disabled reason => .error (.disabled key reason)

instance
  {Key Details : Type}
  [ToJson Key]
  [ToJson Details]
  : ToJson (LookupResults Key Details) where
  toJson results := Json.mkObj [("found", toJson results.found), ("more", toJson results.more)]

instance
  {Key Details : Type}
  [ToJson Key]
  [FromJson Key]
  [FromJson Details]
  : FromJson (LookupResults Key Details) where
  fromJson? json := do
    let found : List (LookupCandidate Key Details) ← json.getObjValAs? _ "found"
    let more ← json.getObjValAs? Bool "more"
    (LookupResults.ofList found more).mapError toString

end Forms.Model
