module

public import Lean.Data.Json
public import Std.Time.Date

@[expose] public section
namespace Forms.Model
open Lean

/-- `mantissa / 10 ^ exponent`, without trailing zeros in the fraction. -/
structure Decimal where
  mantissa : Int
  exponent : Nat
  normalized : exponent = 0 ∨ mantissa % 10 ≠ 0
  deriving DecidableEq

def Decimal.normalize (mantissa : Int) : (exponent : Nat) → Decimal
  | 0 => ⟨mantissa, 0, .inl rfl⟩
  | exponent + 1 =>
    if h : mantissa % 10 = 0 then normalize (mantissa / 10) exponent
    else ⟨mantissa, exponent + 1, .inr h⟩

theorem Decimal.normalize_self (value : Decimal) :
    Decimal.normalize value.mantissa value.exponent = value := by
  obtain ⟨mantissa, exponent, normalized⟩ := value
  cases exponent with
  | zero => rfl
  | succ exponent =>
    have : mantissa % 10 ≠ 0 := by omega
    simp [normalize, this]

def Uuid.hexDigits : List Char :=
  ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']

def Uuid.canonicalFrom : (characters : List Char) → (position : Nat) → Bool
  | [], position => position == 36
  | c :: rest, position =>
    (if position ∈ [8, 13, 18, 23] then c == '-' else c ∈ Uuid.hexDigits) &&
      canonicalFrom rest (position + 1)

/-- Lowercase, in the 8-4-4-4-12 hexadecimal form; literals are checked `by decide`. -/
def Uuid.isCanonical (text : String) : Bool :=
  Uuid.canonicalFrom text.toList 0

structure Uuid where
  value : String
  canonical : Uuid.isCanonical value
  deriving DecidableEq

instance : Repr Uuid where
  reprPrec uuid _ := repr uuid.value

def Int32.ofInt? (value : Int) : Option Int32 :=
  if h : Int32.minValue.toInt ≤ value ∧ value ≤ Int32.maxValue.toInt then
    some (Int32.ofIntLE value h.1 h.2)
  else
    none

def Int64.ofInt? (value : Int) : Option Int64 :=
  if h : Int64.minValue.toInt ≤ value ∧ value ≤ Int64.maxValue.toInt then
    some (Int64.ofIntLE value h.1 h.2)
  else
    none

theorem Int32.ofInt?_toInt (value : Int32) : Int32.ofInt? value.toInt = some value := by
  have := Int32.le_toInt value
  simp [Int32.ofInt?, Int32.toInt_le, Int32.ofIntLE_toInt]
  omega

theorem Int64.ofInt?_toInt (value : Int64) : Int64.ofInt? value.toInt = some value := by
  have := Int64.le_toInt value
  simp [Int64.ofInt?, Int64.toInt_le, Int64.ofIntLE_toInt]
  omega

instance : ToJson Int32 := ⟨(toJson ·.toInt)⟩

instance : FromJson Int32 where
  fromJson? json := do
    let value : Int ← fromJson? json
    (Int32.ofInt? value).elim (throw s!"Out of range for a 32-bit integer: {value}") pure

end Forms.Model
