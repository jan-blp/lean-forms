module

public import Forms.Runtime.Identity
public import Forms.Runtime.Feedback

@[expose] public section

namespace Forms.Runtime.Display

/-- A control's position in the component tree, as zero-based child indices; actions are decoded
along it. -/
structure Target where
  indices : List Nat := []
  deriving BEq

def Target.child (target : Target) (index : Nat) : Target :=
  ⟨target.indices ++ [index]⟩

structure ChoiceOption where
  value : String
  label : String
  deriving BEq

inductive Editor where
  | text (value : String)
  | natural (value : Nat)
  | checkbox (value : Bool)
  /-- `selected` is the active option's `value`, or empty when no option matches. -/
  | choice (selected : String) (options : List ChoiceOption)
  /-- A button; its argument is ignored. -/
  | action
  deriving BEq

structure Control where
  key : ControlKey
  target : Target
  label : String
  disabled : Bool
  location : Feedback.Location
  input : Editor
  messages : Option String := none
  deriving BEq

inductive View where
  | hidden
  | control (control : Control)
  | stack (label : Option String) (children : List View)
  | computed (label text : String)
  /-- Items, then the add button; `messages` are about the list as a whole. -/
  | list (label : String) (children : List View) (messages : Option String)
  deriving BEq

mutual
/-- The controls of `view`, in display order. -/
def View.controls : View → List Control
  | .control c => [c]
  | .stack _ children => View.controlsAll children
  | .list _ children _ => View.controlsAll children
  | .hidden => []
  | .computed .. => []

def View.controlsAll : List View → List Control
  | [] => []
  | view :: rest => view.controls ++ View.controlsAll rest
end

def duplicateNote : String := "Duplicate control: this value is edited elsewhere in the form."

mutual
/-- Replaces each control whose key is in `seen` with a note; returns the keys seen after. -/
def View.dedupeFrom (seen : List ControlKey) : View → View × List ControlKey
  | .control c =>
    if c.key ∈ seen then
      (.computed c.label duplicateNote, seen)
    else
      (.control c, c.key :: seen)
  | .stack label children =>
    let result := View.dedupeAll seen children
    (.stack label result.1, result.2)
  | .list label children messages =>
    let result := View.dedupeAll seen children
    (.list label result.1 messages, result.2)
  | .hidden => (.hidden, seen)
  | .computed label text => (.computed label text, seen)

def View.dedupeAll (seen : List ControlKey) : List View → List View × List ControlKey
  | [] => ([], seen)
  | view :: rest =>
    let head := view.dedupeFrom seen
    let tail := View.dedupeAll head.2 rest
    (head.1 :: tail.1, tail.2)
end

/-- Replaces each control whose key appeared earlier with a note. -/
def View.dedupe (view : View) : View :=
  (view.dedupeFrom []).1

mutual
theorem View.dedupeFrom_spec
  (seen : List ControlKey)
  (view : View)
  (nodup : seen.Nodup)
  : (view.dedupeFrom seen).2 =
      ((view.dedupeFrom seen).1.controls.map (·.key)).reverse ++ seen ∧
    (view.dedupeFrom seen).2.Nodup := by
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
  : (View.dedupeAll seen views).2 =
      ((View.controlsAll (View.dedupeAll seen views).1).map (·.key)).reverse ++ seen ∧
    (View.dedupeAll seen views).2.Nodup := by
  match views with
  | [] => simp [View.dedupeAll, View.controlsAll, nodup]
  | view :: rest =>
    have head := View.dedupeFrom_spec seen view nodup
    have tail := View.dedupeAll_spec (view.dedupeFrom seen).2 rest head.2
    refine ⟨?_, ?_⟩
    · simp only [View.dedupeAll, View.controlsAll]
      rw [tail.1, head.1]
      simp
    · simpa [View.dedupeAll] using tail.2
end

/-- No two controls of a deduplicated view share a key. -/
theorem View.dedupe_keys_nodup (view : View) : (view.dedupe.controls.map (·.key)).Nodup := by
  have spec := View.dedupeFrom_spec [] view List.nodup_nil
  have keys : ((view.dedupeFrom []).1.controls.map (·.key)).reverse.Nodup := by
    have nodup := spec.2
    rw [spec.1, List.append_nil] at nodup
    exact nodup
  unfold List.Nodup at keys
  exact (List.pairwise_reverse.mp keys).imp Ne.symm

def View.title (view : View) : String :=
  let label := match view with
    | .control c => c.label
    | .stack label _ => label.getD ""
    | .list label .. => label
    | .computed label .. => label
    | _ => ""
  if label.isEmpty then "Form" else label

end Forms.Runtime.Display
