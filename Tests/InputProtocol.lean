module

public import Forms.Runtime.InputProtocol
public import Forms.Runtime.JsonProtocol

@[expose] public section

namespace Tests.InputProtocol
open Lean Forms.Runtime

def expect (ty : Forms.DataType) (value expected : Json) : IO Unit := do
  let actual ← IO.ofExcept (InputProtocol.fromJson value >>= Input.decode ty)
  let actual := JsonProtocol.valueToJson actual
  unless actual == expected do
    throw (IO.userError s!"Normalization: expected {expected.compress}, got {actual.compress}")

def reject (ty : Forms.DataType) (value : Json) : IO Unit := do
  match InputProtocol.fromJson value >>= Input.decode ty with
  | .error _ => pure ()
  | .ok actual => throw (IO.userError s!"Unexpected normalization: {(JsonProtocol.valueToJson actual).compress}")

def run : IO Unit := do
  expect .natural (toJson " \t003\r\n") (toJson "3")
  expect .natural (toJson "000123456789012345678901234567890") (toJson "123456789012345678901234567890")
  for input in ["", " ", "-1", "+1", "1.5", "1e3", "0x10", "1 2", "1_000", "_1", "1_", "١", "1\x00"] do
    reject .natural (toJson input)
  reject .natural (toJson (1 : Nat))
  for input in ["0001-01-01", "9999-12-31", "2000-02-29", "2028-02-29"] do
    expect .date (toJson input) (toJson input)
  for input in ["0000-01-01", "1900-02-29", "2028-02-30", "2028-2-29", " 2028-02-29"] do
    reject .date (toJson input)
  expect .text (toJson " 🌍\x00 ") (toJson " 🌍\x00 ")
  expect .boolean (toJson false) (toJson false)
  IO.println "PASS: editor normalization uses Lean value decoding"

end Tests.InputProtocol
