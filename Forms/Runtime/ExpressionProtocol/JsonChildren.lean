module

import all Lean.Data.Json.Basic -- for JSON decoding proofs
public import Forms.Runtime.JsonProtocol

@[expose] public section

namespace Forms.Runtime.ExpressionProtocol
open Lean Std.DTreeMap.Internal

theorem lookup_lt (tree : Impl String (fun _ => Json)) (key : String) (value : Json)
    (h : Impl.Const.get? tree key = some value) : sizeOf value < sizeOf tree := by
  induction tree with
  | leaf => simp [Impl.Const.get?] at h
  | inner => simp only [Impl.Const.get?] at h; split at h <;> simp_all <;> omega

/-- Successful object lookup returns a structurally smaller JSON value. -/
theorem sizeOf_field (json child : Json) (key : String) (h : json.getObjVal? key = .ok child) :
    sizeOf child < sizeOf json := by
  rcases json with _ | _ | _ | _ | _ | ⟨⟨⟨tree⟩⟩⟩ <;>
    simp [Json.getObjVal?, pure, Except.pure, throw] at h
  split at h <;> simp_all
  have := lookup_lt tree key child ‹_›
  omega

/-- A JSON child carries the size bound needed by the total decoders. -/
abbrev Child (parent : Json) := { child : Json // sizeOf child < sizeOf parent }

/-- Object lookup with an erased proof for well-founded recursion. -/
def childField (json : Json) (key : String) : Except String (Child json) :=
  match h : json.getObjVal? key with
  | .ok value => .ok ⟨value, sizeOf_field json value key h⟩
  | .error error => .error error

/-- Array elements with erased proofs for well-founded recursion. -/
def childElements (json : Json) : Except String (Array (Child json)) :=
  match json with
  | .arr items => .ok (items.attach.map fun item => ⟨item.val, by
      have := Array.sizeOf_lt_of_mem item.property; simp; omega⟩)
  | _ => .error "array expected"

end Forms.Runtime.ExpressionProtocol
