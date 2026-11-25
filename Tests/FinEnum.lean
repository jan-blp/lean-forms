module

import Mathlib.Data.FinEnum
public meta import Forms.Deriving.FinEnum

namespace Tests.FinEnum

private inductive Side where
  | left
  | right
  deriving DecidableEq, FinEnum

private inductive Pair where
  | none
  | one (side : Side)
  | two (first : Side) (second : Side)
  deriving DecidableEq, FinEnum

/-- Constructors with fields are listed once per combination of their values. -/
example : FinEnum.card Pair = 7 := by
  decide

example : FinEnum.toList Pair =
    [.none, .one .left, .one .right, .two .left .left, .two .left .right, .two .right .left,
      .two .right .right] := by
  decide

end Tests.FinEnum
