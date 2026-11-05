module

public import Forms.Core.Composition

@[expose] public section

namespace Forms

/-- Paths read from an expression's input. -/
def Expr.dependencies {input result : DataType} : Expr input result → List (PathFrom input)
  | .value _ => []
  | .project path => [⟨path⟩]
  | .all items _ context => items.dependencies ++ [⟨context⟩]
  | .sum items _ | .filter items _ | .sortBy items _ _
  | .sortNatBy items _ _ | .length items => items.dependencies
  | .cases subject _ | .enumLabel subject => subject.dependencies
  | .search items _ query => items.dependencies ++ query.dependencies
  | .snoc items expression => items.dependencies ++ expression.dependencies
  | .enumCases (domain := domain) subject branches =>
      subject.dependencies ++ (FinEnum.toList domain).flatMap (fun i => (branches i).dependencies)
  | .ifThenElse condition yes no => condition.dependencies ++ yes.dependencies ++ no.dependencies
  | .natToText operand | .not operand => operand.dependencies
  | .enumEq left right | .textEq left right | .textAppend left right
  | .natAdd left right | .natSub left right | .natMul left right
  | .and left right | .dateLe left right | .natLe left right =>
      left.dependencies ++ right.dependencies

/-- Display dependencies, excluding children and action bodies. -/
def Composition.Component.dependencies {state : DataType} : Component state → List (PathFrom state)
  | .stack .. | .button .. => []
  | .field path .. | .list path .. | .sum path .. | .actionWidget path .. => [⟨path⟩]
  | .computed _ expression | .text expression => expression.dependencies
  | .table rows _ => rows.dependencies
  | .visibleWhen condition _ | .disabledWhen condition _ => condition.dependencies

end Forms
