module

public import Forms.Core.Component.Builder

@[expose] public section

namespace Forms.ExampleForms.TestReport

open Composition

inductive Provider where
  | bedrock
  | vertex
  deriving DecidableEq, BEq

instance : FinEnum Provider :=
  FinEnum.ofList [.bedrock, .vertex] (by grind [Provider])

def providerEnum : Enum where
  type := Provider
  label
    | .bedrock => "Bedrock"
    | .vertex => "Vertex"

inductive ProviderFilter where
  | all
  | provider (value : Provider)
  deriving DecidableEq, BEq

instance : FinEnum ProviderFilter :=
  FinEnum.ofList [.all, .provider .bedrock, .provider .vertex] (by grind [ProviderFilter, Provider])

def providerFilterEnum : Enum where
  type := ProviderFilter
  label
    | .all => "All"
    | .provider value => providerEnum.label value
  label_injective := by grind [Function.Injective, providerEnum, Provider]

inductive FilterField where
  | provider
  | failuresOnly
  deriving DecidableEq

instance : FinEnum FilterField :=
  FinEnum.ofList [.provider, .failuresOnly] (by grind [FilterField])

def filterFields : Enum where
  type := FilterField
  label
    | .provider => "provider"
    | .failuresOnly => "failuresOnly"

abbrev filtersShape : DataType := .record filterFields fun
  | .provider => .enum providerFilterEnum
  | .failuresOnly => .boolean

def filtersForm {state : DataType} : Component.Builder state filtersShape :=
  Component.Builder.group "Filters" fun
    | .provider => Component.Builder.field "Provider" .select
    | .failuresOnly => Component.Builder.field "Failures only" .checkbox

inductive SortOrder where
  | nameAscending
  | nameDescending
  | provider
  deriving DecidableEq

instance : FinEnum SortOrder :=
  FinEnum.ofList [.nameAscending, .nameDescending, .provider] (by grind [SortOrder])

def sortOrderEnum : Enum where
  type := SortOrder
  label
    | .nameAscending => "Name ascending"
    | .nameDescending => "Name descending"
    | .provider => "Provider"

inductive ResultField where
  | name
  | provider
  | passed
  deriving DecidableEq

instance : FinEnum ResultField :=
  FinEnum.ofList [.name, .provider, .passed] (by grind [ResultField])

def resultFields : Enum where
  type := ResultField
  label
    | .name => "name"
    | .provider => "provider"
    | .passed => "passed"

abbrev resultShape : DataType := .record resultFields fun
  | .name => .text
  | .provider => .enum providerEnum
  | .passed => .boolean

inductive ReportField where
  | filters
  | sort
  | results
  deriving DecidableEq

instance : FinEnum ReportField :=
  FinEnum.ofList [.filters, .sort, .results] (by grind [ReportField])

def reportFields : Enum where
  type := ReportField
  label
    | .filters => "filters"
    | .sort => "sort"
    | .results => "results"

abbrev reportShape : DataType := .record reportFields fun
  | .filters => filtersShape
  | .sort => .enum sortOrderEnum
  | .results => .list resultShape

def filtersPath : Path reportShape filtersShape := .field .filters .self

def sortPath : Path reportShape (.enum sortOrderEnum) := .field .sort .self

def providerResults (value : ⟦reportShape⟧) : List ⟦resultShape⟧ :=
  match value .filters .provider with
  | .all => value .results
  | .provider selected => (value .results).filter fun row => ((row .provider : Provider) == selected)

def statusResults (value : ⟦reportShape⟧) : List ⟦resultShape⟧ :=
  if value .filters .failuresOnly then
    (providerResults value).filter fun row => !row .passed
  else providerResults value

def visibleResults (value : ⟦reportShape⟧) : List ⟦resultShape⟧ :=
  (statusResults value).mergeSort fun left right =>
    match value .sort with
    | .nameAscending => left .name ≤ right .name
    | .nameDescending => right .name ≤ left .name
    | .provider => providerEnum.label (left .provider) ≤ providerEnum.label (right .provider)

def summary (value : ⟦reportShape⟧) : String :=
  let results := providerResults value
  s!"{(results.filter fun row => row .passed).length}/{results.length} passed"

def columns : List (Column resultShape) :=
  [{ label := "Test", format := fun row => row .name },
   { label := "Provider", format := fun row => providerEnum.label (row .provider) },
   { label := "Result", format := fun row => if row .passed then "PASS" else "FAIL" }]

inductive ReportSection where
  | filters
  | sort
  | summary
  | results
  deriving DecidableEq

instance : FinEnum ReportSection :=
  FinEnum.ofList [.filters, .sort, .summary, .results] (by grind [ReportSection])

def reportSections : Enum where
  type := ReportSection
  label
    | .filters => "Filters"
    | .sort => "Sort"
    | .summary => "Summary"
    | .results => "Results"

def report : Component reportShape := .stack none (items := reportSections) fun
  | .filters => filtersForm filtersPath
  | .sort => .field sortPath "Sort" .select
  | .summary => .text summary
  | .results => .table visibleResults columns

def result (name : String) (provider : Provider) (passed : Bool) : ⟦resultShape⟧
  | .name => name
  | .provider => provider
  | .passed => passed

def initial : ⟦reportShape⟧
  | .filters => fun
      | .provider => .all
      | .failuresOnly => false
  | .sort => .nameAscending
  | .results =>
      [result "Zulu" .bedrock false,
       result "Alpha" .vertex true,
       result "Beta" .bedrock true,
       result "Delta" .vertex false]

end Forms.ExampleForms.TestReport
