module

public import Forms.Core.Composition
public import Mathlib.Data.List.Dedup

@[expose] public section

namespace Forms

/-- Paths read from an expression's input. -/
def Expr.dependencies {input result : DataType} (expression : Expr input result) :
    {paths : List (PathFrom input) // paths.Nodup} :=
  ⟨(collect expression).dedup, List.nodup_dedup _⟩
where
  collect {input result : DataType} : Expr input result → List (PathFrom input)
    | .value _ => []
    | .project path => [⟨path⟩]
    | .all items _ context => collect items ++ [⟨context⟩]
    | .sum items _ | .filter items _ | .sortBy items _ _
    | .sortNatBy items _ _ | .length items => collect items
    | .cases subject _ | .enumLabel subject => collect subject
    | .search items _ query => collect items ++ collect query
    | .snoc items expression => collect items ++ collect expression
    | .enumCases (domain := domain) subject branches =>
        collect subject ++ (FinEnum.toList domain).flatMap (fun i => collect (branches i))
    | .ifThenElse condition yes no => collect condition ++ collect yes ++ collect no
    | .natToText operand | .not operand => collect operand
    | .enumEq left right | .textEq left right | .textAppend left right
    | .natAdd left right | .natSub left right | .natMul left right
    | .and left right | .dateLe left right | .natLe left right =>
        collect left ++ collect right

namespace Composition.Component

/-- Paths read from a component's input, excluding children and action bodies. -/
def dependencies {state : DataType} : Component state → {paths : List (PathFrom state) // paths.Nodup}
  | .stack .. | .button .. => ⟨[], by simp⟩
  | .field path .. | .list path .. | .sum path .. | .actionWidget path .. => ⟨[⟨path⟩], by simp⟩
  | .computed _ expression | .text expression => expression.dependencies
  | .table rows _ => rows.dependencies
  | .visibleWhen condition _ | .disabledWhen condition _ => condition.dependencies

end Composition.Component

end Forms
