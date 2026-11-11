module

public import Forms.Runtime.Display

public section
namespace Forms.Runtime.Display

mutual
theorem View.dedupeFrom_spec
  (seen : List ControlKey)
  (view : View)
  (nodup : seen.Nodup)
  : (view.dedupeFrom seen).seen =
      ((view.dedupeFrom seen).deduped.controls.map (·.key)).reverse ++ seen ∧
    (view.dedupeFrom seen).seen.Nodup := by
  match view with
  | .control c =>
    by_cases h : c.key ∈ seen
    · simp [View.dedupeFrom, h, View.controls, nodup]
    · simp [View.dedupeFrom, h, View.controls, nodup]
  | .stack label children =>
    have := View.dedupeAll_spec seen children nodup
    simpa [View.dedupeFrom, View.controls] using this
  | .list label children messages =>
    have := View.dedupeAll_spec seen children nodup
    simpa [View.dedupeFrom, View.controls] using this
  | .hidden => simp [View.dedupeFrom, View.controls, nodup]
  | .computed .. => simp [View.dedupeFrom, View.controls, nodup]

theorem View.dedupeAll_spec
  (seen : List ControlKey)
  (views : List View)
  (nodup : seen.Nodup)
  : (View.dedupeAll seen views).seen =
      ((View.controlsAll (View.dedupeAll seen views).deduped).map (·.key)).reverse ++ seen ∧
    (View.dedupeAll seen views).seen.Nodup := by
  match views with
  | [] => simp [View.dedupeAll, View.controlsAll, nodup]
  | view :: rest =>
    have ⟨head_keys, head_nodup⟩ := View.dedupeFrom_spec seen view nodup
    have ⟨tail_keys, tail_nodup⟩ := View.dedupeAll_spec (view.dedupeFrom seen).seen rest head_nodup
    refine ⟨?_, ?_⟩
    · simp only [View.dedupeAll, View.controlsAll]
      rw [tail_keys, head_keys]
      simp
    · simpa [View.dedupeAll] using tail_nodup
end

/-- No two controls of a deduplicated view share a key. -/
theorem View.dedupe_keys_nodup (view : View) : (view.dedupe.controls.map (·.key)).Nodup := by
  have ⟨seen_keys, nodup⟩ := View.dedupeFrom_spec [] view List.nodup_nil
  have keys : ((view.dedupeFrom []).deduped.controls.map (·.key)).reverse.Nodup := by
    rw [seen_keys, List.append_nil] at nodup
    exact nodup
  unfold List.Nodup at keys
  exact (List.pairwise_reverse.mp keys).imp Ne.symm

end Forms.Runtime.Display
