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
  deriving DecidableEq, Repr

def Decimal.normalize (mantissa : Int) : (exponent : Nat) → Decimal
  | 0 => ⟨mantissa, 0⟩
  | exponent + 1 =>
    if mantissa % 10 == 0 then normalize (mantissa / 10) exponent else ⟨mantissa, exponent + 1⟩

def Decimal.toString (value : Decimal) : String :=
  let digits := value.mantissa.natAbs.repr
  let digits := "".pushn '0' (value.exponent + 1 - digits.length) ++ digits
  let whole := (digits.take (digits.length - value.exponent)).toString
  let fraction := (digits.drop (digits.length - value.exponent)).toString
  let sign := if value.mantissa < 0 then "-" else ""
  if fraction.isEmpty then sign ++ whole else s!"{sign}{whole}.{fraction}"

instance : ToString Decimal := ⟨Decimal.toString⟩

instance : ToJson Decimal where
  toJson value := .num ⟨value.mantissa, value.exponent⟩

instance : FromJson Decimal where
  fromJson? json := do
    let number ← json.getNum?
    pure (Decimal.normalize number.mantissa number.exponent)

def Uuid.canonicalFrom : (characters : List Char) → (position : Nat) → Bool
  | [], position => position == 36
  | c :: rest, position =>
    (if position ∈ [8, 13, 18, 23] then c == '-' else c.isDigit || ('a' ≤ c && c ≤ 'f')) &&
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

def Uuid.ofString? (text : String) : Option Uuid :=
  let text := text.toLower
  if h : Uuid.isCanonical text then some ⟨text, h⟩ else none

instance : ToJson Uuid where
  toJson uuid := .str uuid.value

instance : FromJson Uuid where
  fromJson? json := do
    let text ← json.getStr?
    match Uuid.ofString? text with
    | some uuid => pure uuid
    | none => throw s!"Invalid UUID: {text}"

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

instance : ToJson Int32 := ⟨(toJson ·.toInt)⟩
instance : ToJson Int64 := ⟨(toJson ·.toInt)⟩

instance : FromJson Int32 where
  fromJson? json := do
    let value : Int ← fromJson? json
    (Int32.ofInt? value).elim (throw s!"Out of range for a 32-bit integer: {value}") pure

instance : FromJson Int64 where
  fromJson? json := do
    let value : Int ← fromJson? json
    (Int64.ofInt? value).elim (throw s!"Out of range for a 64-bit integer: {value}") pure

open Std.Time in
/-- ISO 8601: `YYYY-MM-DD`, with a four-digit year. -/
def Date.toIso (date : PlainDate) : String :=
  let pad (width : Nat) (value : Int) :=
    "".pushn '0' (width - (toString value).length) ++ toString value
  s!"{pad 4 date.year.toInt}-{pad 2 date.month.val}-{pad 2 date.day.val}"

open Std.Time in
def Date.ofIso? (text : String) : Option PlainDate := do
  let [year, month, day] := text.splitOn "-" | none
  guard (year.length == 4 && month.length == 2 && day.length == 2)
  guard ([year, month, day].all (·.all Char.isDigit))
  let year ← year.toNat?
  let month ← month.toNat?
  let day ← day.toNat?
  if hm : 1 ≤ month ∧ month ≤ 12 then
    if hd : 1 ≤ day ∧ day ≤ 31 then
      PlainDate.ofYearMonthDay? (.ofInt year) (Month.Ordinal.ofNat month hm)
        (Day.Ordinal.ofNat day hd)
    else none
  else none

instance : ToJson Std.Time.PlainDate := ⟨(.str <| Date.toIso ·)⟩

instance : FromJson Std.Time.PlainDate where
  fromJson? json := do
    let text ← json.getStr?
    (Date.ofIso? text).elim (throw s!"Invalid date: {text}") pure

end Forms.Model
