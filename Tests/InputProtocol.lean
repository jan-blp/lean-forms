module

public import Forms.Runtime.InputProtocol

@[expose] public section

namespace Tests.InputProtocol
open Lean Forms.Runtime

def decode {α : Type} (ty : Forms.Model.Editor α) (value : Json) : Except String α :=
  InputProtocol.fromJson value >>= fun input => (Input.decode ty input).mapError toString

def expect {α : Type} [ToJson α] (ty : Forms.Model.Editor α) (value expected : Json) : IO Unit := do
  let actual ← IO.ofExcept (decode ty value)
  let actual := toJson actual
  unless actual == expected do
    throw (IO.userError s!"Normalization: expected {expected.compress}, got {actual.compress}")

def reject {α : Type} [ToJson α] (ty : Forms.Model.Editor α) (value : Json) : IO Unit := do
  match decode ty value with
  | .error _ => pure ()
  | .ok actual => throw (IO.userError s!"Unexpected normalization: {(toJson actual).compress}")

def run : IO Unit := do
  expect .natural (toJson " \t003\r\n") (toJson (3 : Nat))
  expect .natural (toJson "000123456789012345678901234567890") (toJson (123456789012345678901234567890 : Nat))
  for input in ["", " ", "-1", "+1", "1.5", "1e3", "0x10", "1 2", "1_000", "_1", "1_", "١", "1\x00"] do
    reject .natural (toJson input)
  reject .natural (toJson (1 : Nat))
  expect .text (toJson " 🌍\x00 ") (toJson " 🌍\x00 ")
  expect .checkbox (toJson false) (toJson false)
  IO.println "PASS: editor normalization uses Lean value decoding"

end Tests.InputProtocol
