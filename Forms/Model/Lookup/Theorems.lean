module

public import Forms.Model.Lookup
import all Lean.Data.Json.Basic

public section
namespace Forms.Model
open Lean

@[simp] theorem LookupKey.toJson_eq (key : LookupKey) :
    toJson key = Json.str key.value := rfl

@[simp] theorem LookupKey.fromJson_toJson (key : LookupKey) :
    fromJson? (toJson key) = .ok key := by
  cases key
  rfl

namespace LookupResults

theorem choose_spec
  {Key Details : Type}
  [ToJson Key]
  {results : LookupResults Key Details}
  {availability : LookupCandidate Key Details → LookupAvailability}
  {key : LookupKey}
  {reference : Reference Key}
  (chosen : results.choose availability key = .ok reference)
  : ∃ candidate ∈ results.found,
      candidate.reference = reference ∧ candidate.wireKey = key ∧ availability candidate = .enabled := by
  cases found : results.found.find? (fun candidate => decide (candidate.wireKey = key)) with
  | none => simp [choose, found] at chosen
  | some candidate =>
    cases available : availability candidate with
    | disabled reason => simp [choose, found, available] at chosen
    | enabled =>
      have reference_eq : candidate.reference = reference := by
        simpa [choose, found, available] using chosen
      exact ⟨candidate, List.mem_of_find?_eq_some found, reference_eq,
        of_decide_eq_true (List.find?_some
          (p := fun (candidate : LookupCandidate Key Details) => decide (candidate.wireKey = key)) found),
        available⟩

variable
  {Key Details : Type}
  [ToJson Key]
  {records : List (LookupCandidate Key Details)}
  {keep : LookupCandidate Key Details → Prop}
  [DecidablePred keep]
  {limit : Nat}
  {result : LookupResults Key Details}

theorem select_found
  (selected : select records keep limit = .ok result)
  : result.found = (records.filter (fun record => decide (keep record))).take limit := by
  unfold select at selected
  dsimp only at selected
  split at selected
  · cases selected
    rfl
  · cases selected

theorem select_kept
  (selected : select records keep limit = .ok result)
  {record : LookupCandidate Key Details}
  (member : record ∈ result.found)
  : keep record := by
  rw [select_found selected] at member
  exact of_decide_eq_true (List.mem_filter.mp (List.mem_of_mem_take member)).2

theorem select_length_le
  (selected : select records keep limit = .ok result)
  : result.found.length ≤ limit := by
  rw [select_found selected]
  exact List.length_take_le _ _

theorem select_more_iff
  (selected : select records keep limit = .ok result)
  : result.more = true ↔ limit < (records.filter (fun record => decide (keep record))).length := by
  unfold select at selected
  dsimp only at selected
  split at selected
  · cases selected
    exact decide_eq_true_iff
  · cases selected

theorem select_more_omitted
  (selected : select records keep limit = .ok result)
  (more : result.more = true)
  : ∃ record ∈ records, keep record ∧ record ∉ result.found := by
  unfold select at selected
  dsimp only at selected
  split at selected
  next distinct =>
    cases selected
    by_contra! all_returned
    have length_le := (List.Nodup.of_map LookupCandidate.wireKey distinct).length_le_of_subset (by
      intro record member
      have kept := List.mem_filter.mp member
      exact all_returned record kept.1 (of_decide_eq_true kept.2))
    dsimp only at length_le more
    have bound := List.length_take_le limit (records.filter (fun record => decide (keep record)))
    have longer := of_decide_eq_true more
    omega
  next repeated => cases selected

end LookupResults
end Forms.Model
