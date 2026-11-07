module

public import Forms.Runtime.JsonProtocol

@[expose] public section

namespace Forms.Runtime.InputProtocol
open Lean

/-- The whitespace accepted by JavaScript's String.trim, preserved for editor inputs. -/
def editorWhitespace (c : Char) : Bool :=
  let n := c.toNat
  (0x09 ≤ n && n ≤ 0x0D) || n == 0x20 || n == 0xA0 || n == 0x1680 ||
    (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 || n == 0x2029 ||
    n == 0x202F || n == 0x205F || n == 0x3000 || n == 0xFEFF

/-- Normalize editor input, keeping transport decoding strict elsewhere. -/
def decode (ty : DataType) (value : Json) : Except String ⟦ty⟧ := do
  let (value, error) ← match ty with
    | .natural => do
      let text ← value.getStr?.mapError (fun _ => "Expected text.")
      let text := ((text.dropWhile editorWhitespace).dropEndWhile editorWhitespace).toString
      pure (toJson text, "Enter a non-negative whole number.")
    | .text => pure (value, "Invalid text value.")
    | .boolean => pure (value, "Invalid boolean value.")
    | .date => pure (value, "Invalid date value.")
    | .enum .. => pure (value, "Invalid enum value.")
    | .list .. => throw "Unsupported value type: list"
    | .record .. => throw "Unsupported value type: record"
    | .sum .. => throw "Unsupported value type: sum"
  (JsonProtocol.valueFromJson ty value).mapError (fun _ => error)

end Forms.Runtime.InputProtocol
