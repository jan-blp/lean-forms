module

public import Forms.Core.DataType

@[expose] public section

namespace Forms.Runtime

inductive Input where
  | text (value : String)
  | boolean (value : Bool)
  | index (value : Nat)

/-- The whitespace accepted by JavaScript's String.trim. -/
def Input.editorWhitespace (c : Char) : Bool :=
  let n := c.toNat
  (0x09 ≤ n && n ≤ 0x0D) || n == 0x20 || n == 0xA0 || n == 0x1680 ||
    (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 || n == 0x2029 ||
    n == 0x202F || n == 0x205F || n == 0x3000 || n == 0xFEFF

def Input.decode (ty : DataType) (input : Input) : Except String ⟦ty⟧ :=
  match ty with
  | .natural => do
    let .text raw := input | throw "Expected text."
    let text := ((raw.dropWhile editorWhitespace).dropEndWhile editorWhitespace).toString
    let some value := if text.all Char.isDigit then text.toNat? else none
      | throw "Enter a non-negative whole number."
    pure value
  | .text => match input with
    | .text value => .ok value
    | _ => .error "Invalid text value."
  | .boolean => match input with
    | .boolean value => .ok value
    | _ => .error "Invalid boolean value."
  | .date => do
    let .text raw := input | throw "Invalid date value."
    let some value := Date.ofString? raw | throw "Invalid date value."
    pure value
  | .enum domain => do
    let .index selected := input | throw "Invalid enum value."
    if h : selected < FinEnum.card domain then pure (FinEnum.equiv.symm ⟨selected, h⟩)
    else throw "Invalid enum value."
  | .list _ => .error "Unsupported value type: list"
  | .record .. => .error "Unsupported value type: record"
  | .sum .. => .error "Unsupported value type: sum"

end Forms.Runtime
