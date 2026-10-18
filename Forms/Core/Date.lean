import Std.Time.Format

namespace Forms

structure Date where
  val : Std.Time.PlainDate
  withinBounds : 1 ≤ val.year ∧ val.year ≤ 9999
  deriving Repr, DecidableEq

namespace Date

def toString (date : Date) : String :=
  Std.Time.PlainDate.toLeanDateString date.val

def ofString? (text : String) : Option Date := do
  let value ← (Std.Time.PlainDate.fromLeanDateString text).toOption
  if h : 1 ≤ value.year ∧ value.year ≤ 9999 then
    let date : Date := { val := value, withinBounds := h }
    if Date.toString date == text then some date else none
  else none

theorem ofString?_sound {text : String} {date : Date}
    (h : ofString? text = some date) : toString date = text := by
  simp only [ofString?, bind, Option.bind] at h
  split at h <;> grind

def le (left right : Date) : Bool := compare left.val right.val != .gt

end Date
end Forms
