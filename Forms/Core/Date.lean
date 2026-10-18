import Std.Time.Format

namespace Forms

abbrev Date := { value : Std.Time.PlainDate // 1 ≤ value.year ∧ value.year ≤ 9999 }

namespace Date

def toString (date : Date) : String :=
  Std.Time.PlainDate.toLeanDateString date.val

def ofString? (text : String) : Option Date := do
  let value ← (Std.Time.PlainDate.fromLeanDateString text).toOption
  if h : 1 ≤ value.year ∧ value.year ≤ 9999 then
    let date : Date := ⟨value, h⟩
    if Date.toString date == text then some date else none
  else none

def le (left right : Date) : Bool := compare left.val right.val != .gt

end Date
end Forms
