module

public import Std.Time.Format
import all Std.Time.Date.Unit.Year

@[expose] public section

namespace Forms

structure Date where
  val : Std.Time.PlainDate
  withinBounds : 1 ≤ val.year ∧ val.year ≤ 9999
  deriving Repr, DecidableEq

namespace Date

def digit (n : Nat) : Char :=
  match n % 10 with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'

def parseDigit : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3 | '4' => some 4
  | '5' => some 5 | '6' => some 6 | '7' => some 7 | '8' => some 8 | '9' => some 9
  | _ => none

theorem parseDigit_digit (n : Nat) : parseDigit (digit n) = some (n % 10) := by
  have h : n % 10 < 10 := Nat.mod_lt _ (by decide)
  unfold digit
  split <;> simp_all [parseDigit] <;> omega

def renderParts (year month day : Nat) : String :=
  String.ofList [digit (year / 1000), digit (year / 100), digit (year / 10), digit year,
    '-', digit (month / 10), digit month, '-', digit (day / 10), digit day]

def parseParts (text : String) : Option (Nat × Nat × Nat) := do
  let [a, b, c, d, '-', e, f, '-', g, h] := text.toList | none
  let a ← parseDigit a
  let b ← parseDigit b
  let c ← parseDigit c
  let d ← parseDigit d
  let e ← parseDigit e
  let f ← parseDigit f
  let g ← parseDigit g
  let h ← parseDigit h
  return (a * 1000 + b * 100 + c * 10 + d, e * 10 + f, g * 10 + h)

theorem parseParts_renderParts (year month day : Nat)
    (hy : year < 10000) (hm : month < 100) (hd : day < 100) :
    parseParts (renderParts year month day) = some (year, month, day) := by
  simp only [parseParts, renderParts, String.toList_ofList, parseDigit_digit,
    bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq]
  omega

def fromParts (year month day : Nat) : Option Date := do
  if hy : 1 ≤ year ∧ year ≤ 9999 then
    if hm : 1 ≤ month ∧ month ≤ 12 then
      if hd : 1 ≤ day ∧ day ≤ 31 then
        let y := Std.Time.Year.Offset.ofNat year
        let m : Std.Time.Month.Ordinal := ⟨month, by omega⟩
        let d : Std.Time.Day.Ordinal := ⟨day, by omega⟩
        if valid : y.Valid m d then
          return ⟨⟨y, m, d, valid⟩, by change (1 : Int) ≤ (year : Int) ∧ (year : Int) ≤ 9999; omega⟩
        else none
      else none
    else none
  else none

def toString (date : Date) : String :=
  renderParts date.val.year.toInt.toNat date.val.month.val.toNat date.val.day.val.toNat

def ofString? (text : String) : Option Date := do
  let (year, month, day) ← parseParts text
  let date ← fromParts year month day
  if Date.toString date == text then some date else none

theorem ofString?_sound {text : String} {date : Date}
    (h : ofString? text = some date) : toString date = text := by
  simp only [ofString?, bind, Option.bind] at h
  split at h <;> grind

theorem fromParts_roundTrip (date : Date) :
    fromParts date.val.year.toInt.toNat date.val.month.val.toNat date.val.day.val.toNat = some date := by
  rcases date with ⟨⟨year, month, day, valid⟩, bounds⟩
  change (1 : Int) ≤ year.toInt ∧ year.toInt ≤ 9999 at bounds
  have hm := month.property
  have hd := day.property
  have yn : 1 ≤ year.toInt.toNat ∧ year.toInt.toNat ≤ 9999 := by omega
  have mn : 1 ≤ month.val.toNat ∧ month.val.toNat ≤ 12 := by omega
  have dn : 1 ≤ day.val.toNat ∧ day.val.toNat ≤ 31 := by omega
  have yc : (year.toInt.toNat : Int) = year.toInt := Int.toNat_of_nonneg (by omega)
  have mc : (month.val.toNat : Int) = month.val := Int.toNat_of_nonneg (by omega)
  have dc : (day.val.toNat : Int) = day.val := Int.toNat_of_nonneg (by omega)
  unfold fromParts
  rw [dite_eq_left yn, dite_eq_left mn, dite_eq_left dn]
  have yearEq : Std.Time.Year.Offset.ofNat year.toInt.toNat = year := yc
  simp only [yearEq, mc, dc]
  have vm : (⟨month.val, by omega⟩ : Std.Time.Month.Ordinal) = month := rfl
  have vd : (⟨day.val, by omega⟩ : Std.Time.Day.Ordinal) = day := rfl
  simp only [vm, vd]
  have good : (Std.Time.Year.Offset.ofNat year.toInt.toNat).Valid
      (⟨month.val.toNat, by omega⟩ : Std.Time.Month.Ordinal)
      (⟨day.val.toNat, by omega⟩ : Std.Time.Day.Ordinal) := by
    simpa only [yearEq, mc, dc, vm, vd] using valid
  rw [dite_eq_left good]
  rfl

theorem ofString?_toString (date : Date) : ofString? (toString date) = some date := by
  have hy := date.withinBounds
  change (1 : Int) ≤ date.val.year.toInt ∧ date.val.year.toInt ≤ 9999 at hy
  have hm := date.val.month.property
  have hd := date.val.day.property
  have parsed := parseParts_renderParts date.val.year.toInt.toNat
    date.val.month.val.toNat date.val.day.val.toNat (by omega) (by omega) (by omega)
  simp only [ofString?, toString, parsed, bind, Option.bind, fromParts_roundTrip]
  simp

def le (a b : Date) : Bool := compare a.val b.val != .gt

instance : LE Date where
  le a b := Date.le a b = true

instance (a b : Date) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (Date.le a b = true))

end Date
end Forms
