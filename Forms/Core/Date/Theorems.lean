module

public import Forms.Core.Date
import all Std.Time.Date.Unit.Year

public section

namespace Forms.Date

theorem parseDigit_digit (n : Nat) : parseDigit (digit n) = some (n % 10) := by
  have h : n % 10 < 10 := Nat.mod_lt _ (by decide)
  unfold digit
  split <;> simp_all [parseDigit] <;> omega

theorem parseParts_renderParts (year month day : Nat)
    (hy : year < 10000) (hm : month < 100) (hd : day < 100) :
    parseParts (renderParts year month day) = some (year, month, day) := by
  simp only [parseParts, renderParts, String.toList_ofList, parseDigit_digit,
    bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq]
  omega

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

end Forms.Date
