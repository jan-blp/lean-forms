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

def le (a b : Date) : Bool := compare a.val b.val != .gt

instance : LE Date where
  le a b := Date.le a b = true

instance (a b : Date) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (Date.le a b = true))

end Date
end Forms
