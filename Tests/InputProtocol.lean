module

public import Forms.Runtime.InputProtocol

@[expose] public section

namespace Tests.InputProtocol
open Lean Forms.Runtime

def expect (schema value expected : Json) : IO Unit := do
  let actual ← IO.ofExcept (InputProtocol.evaluate schema value)
  unless actual == expected do
    throw (IO.userError s!"Normalization: expected {expected.compress}, got {actual.compress}")

def reject (schema value : Json) : IO Unit := do
  match InputProtocol.evaluate schema value with
  | .error _ => pure ()
  | .ok actual => throw (IO.userError s!"Unexpected normalization: {actual.compress}")

def run : IO Unit := do
  let natural := Json.mkObj [("kind", toJson "natural")]
  expect natural (toJson " \t003\r\n") (toJson "3")
  expect natural (toJson "000123456789012345678901234567890") (toJson "123456789012345678901234567890")
  for input in ["", " ", "-1", "+1", "1.5", "1e3", "0x10", "1 2", "١", "1\x00"] do
    reject natural (toJson input)
  reject natural (toJson (1 : Nat))
  let date := Json.mkObj [("kind", toJson "date")]
  for input in ["0001-01-01", "9999-12-31", "2000-02-29", "2028-02-29"] do
    expect date (toJson input) (toJson input)
  for input in ["0000-01-01", "1900-02-29", "2028-02-30", "2028-2-29", " 2028-02-29"] do
    reject date (toJson input)
  let enum := Json.mkObj [("kind", toJson "enum"), ("options", toJson ["A", "B"])]
  expect enum (toJson (1 : Nat)) (toJson (1 : Nat))
  reject enum (toJson (2 : Nat))
  reject enum (toJson "1")
  expect (Json.mkObj [("kind", toJson "text")]) (toJson " 🌍\x00 ") (toJson " 🌍\x00 ")
  expect (Json.mkObj [("kind", toJson "boolean")]) (toJson false) (toJson false)
  IO.println "PASS: editor normalization uses Lean value decoding"

end Tests.InputProtocol
