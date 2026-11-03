import Forms.Runtime.JsonProtocol

namespace Forms.Runtime.ExpressionProtocol
open Lean Std.DTreeMap.Internal

private theorem lookup_lt (tree : Impl String (fun _ => Json)) (key : String) (value : Json)
    (h : Impl.Const.get? tree key = some value) : sizeOf value < sizeOf tree := by
  induction tree with
  | leaf => simp [Impl.Const.get?] at h
  | inner sz k v l r ihl ihr =>
    simp only [Impl.Const.get?] at h
    split at h
    · have := ihl h; simp only [Impl.inner.sizeOf_spec]; omega
    · have := ihr h; simp only [Impl.inner.sizeOf_spec]; omega
    · cases h; simp only [Impl.inner.sizeOf_spec]; omega

/-- Successful object lookup returns a structurally smaller JSON value. -/
theorem sizeOf_field (json child : Json) (key : String) (h : json.getObjVal? key = .ok child) :
    sizeOf child < sizeOf json := by
  cases json <;> simp only [Json.getObjVal?, pure, Except.pure, throw] at h
  all_goals try contradiction
  rename_i tree
  split at h
  · rename_i value hv
    cases h
    have small := lookup_lt tree.inner.inner key child hv
    cases tree with
    | mk tree =>
      cases tree with
      | mk tree =>
        simp only [Json.obj.sizeOf_spec, Std.TreeMap.Raw.mk.sizeOf_spec,
          Std.DTreeMap.Raw.mk.sizeOf_spec] at *
        omega
  · contradiction

/-- A JSON child carries the size bound needed by the total decoders. -/
abbrev Child (parent : Json) := { child : Json // sizeOf child < sizeOf parent }

/-- Object lookup with an erased proof for well-founded recursion. -/
def childField (json : Json) (key : String) : Except String (Child json) :=
  match h : json.getObjVal? key with
  | .ok value => .ok ⟨value, sizeOf_field json value key h⟩
  | .error error => .error error

theorem childField_ok {json value : Json} {key : String} (h : json.getObjVal? key = .ok value) :
    childField json key = .ok ⟨value, sizeOf_field json value key h⟩ := by
  unfold childField
  split
  · rename_i found he
    have same : found = value := Except.ok.inj (he.symm.trans h)
    subst found
    rfl
  · rename_i error he
    cases he.symm.trans h

/-- Array elements with erased proofs for well-founded recursion. -/
def childElements (json : Json) : Except String (Array (Child json)) :=
  match json with
  | .arr items => .ok (items.attach.map fun item => ⟨item.val, by
      have := Array.sizeOf_lt_of_mem item.property
      simp only [Json.arr.sizeOf_spec]
      omega⟩)
  | _ => .error "array expected"

end Forms.Runtime.ExpressionProtocol
