import Forms.Runtime.CompositionProtocol
import Forms.ExampleForms.TestReport
import Forms.Runtime.FormSnapshot

namespace Tests.Composition

open Forms Forms.Runtime
open Forms.Composition
open Forms.ExampleForms.TestReport

private def check (name : String) (passed : Bool) : IO Unit := do
  if passed then IO.println ("PASS " ++ name)
  else throw (IO.userError ("FAIL " ++ name))

private def names (value : ⟦reportShape⟧) : List String :=
  (visibleResults.eval value).map fun entry => entry .name

private def tableRows (snapshot : FormSnapshot) : List (List String) :=
  match snapshot with
  | .table _ rows => rows
  | .stack children => children.flatMap tableRows
  | _ => []

private def texts (snapshot : FormSnapshot) : List String :=
  match snapshot with
  | .text value => [value]
  | .stack children => children.flatMap texts
  | _ => []

private def labels (snapshot : FormSnapshot) : List String :=
  match snapshot with
  | .fields fields => fields.flatMap (·.labels)
  | .stack children => children.flatMap labels
  | _ => []

private inductive OuterField where
  | report
  | title
  deriving DecidableEq

private instance : FinEnum OuterField := FinEnum.ofList [.report, .title] (by grind [OuterField])

private def outerFields : Enum where
  type := OuterField
  label
    | .report => "report"
    | .title => "title"

private abbrev outerShape : DataType := .record outerFields fun
  | .report => reportShape
  | .title => .text

private def nestedReport : Component outerShape := .weaken (.field .report .self) report

private def outerInitial : ⟦outerShape⟧
  | .report => initial
  | .title => "Unchanged title"

private theorem pathGetAfterSet {root t : DataType} (path : Path root t) (value : ⟦t⟧)
    (state : ⟦root⟧) : path.get (path.set value state) = value := by
  induction path with
  | self => rfl
  | field index rest ih => simpa [Path.get, Path.set] using ih value (state index)

private def filtersComponent : Component filtersShape :=
  .stack none (items := filterFields) fun
    | .provider => filtersForm .self
    | .failuresOnly => .field (.field .failuresOnly .self) "Only failures" .checkbox

private def setProviderFilter (provider : ProviderFilter) : ⟦reportShape⟧ → ⟦reportShape⟧ :=
  (Path.field .filters (.field .provider .self) : Path reportShape (.enum providerFilterEnum)).set provider

private def setFailuresOnly (enabled : Bool) : ⟦reportShape⟧ → ⟦reportShape⟧ :=
  (Path.field .filters (.field .failuresOnly .self) : Path reportShape .boolean).set enabled

private def setSortOrder (sort : SortOrder) : ⟦reportShape⟧ → ⟦reportShape⟧ :=
  sortPath.set sort

private def testFilteringAndSorting : IO Unit := do
  let selectProvider := setProviderFilter (.provider .bedrock)
  let enableFailures := setFailuresOnly true
  let selected := selectProvider initial
  let filtered := enableFailures selected
  check "TestInitialResultsSorted"
    (names initial == ["Alpha", "Beta", "Delta", "Zulu"])
  check "TestBoundProviderFiltersRows"
    (names selected == ["Beta", "Zulu"])
  check "TestBoundStatusFiltersRows"
    (names filtered == ["Zulu"])
  check "TestStatusFilterPreservesSummaryDenominator"
    (summary.eval selected == "1/2 passed" && summary.eval filtered == "1/2 passed")
  check "TestCombinedFiltersUseCurrentState"
    (filtered .filters .provider == .provider .bedrock && filtered .filters .failuresOnly)
  let reversed := selectProvider (enableFailures initial)
  check "TestIndependentFilterUpdatesCommute"
    (names reversed == names filtered && summary.eval reversed == summary.eval filtered)
  let sorted := (setSortOrder .nameDescending) selected
  check "TestBoundSortPreservesFilters"
    (names sorted == ["Zulu", "Beta"] && summary.eval sorted == summary.eval selected)
  let resetProvider := (setProviderFilter .all) filtered
  check "TestResetProviderPreservesStatusFilter"
    (names resetProvider == ["Delta", "Zulu"])
  check "TestRawResultsRemainUnchanged"
    ((filtered .results).map (fun entry => entry .name) == ["Zulu", "Alpha", "Beta", "Delta"])

private def testRendering : IO Unit := do
  let selected := (setProviderFilter (.provider .bedrock)) initial
  let filtered := (setFailuresOnly true) selected
  let snapshot := FormSnapshot.render report filtered
  check "TestRenderedTableUsesCurrentFilters"
    (tableRows snapshot == [["Zulu", "Bedrock", "FAIL"]])
  check "TestRenderedSummaryUsesBroaderScope"
    (texts snapshot == ["1/2 passed"])
  check "TestExistingFormEditorsRemainRenderable"
    ((labels snapshot).contains "Provider" && (labels snapshot).contains "Sort")

private def testWeakenedRendering : IO Unit := do
  let selected := setFailuresOnly true (setProviderFilter (.provider .bedrock) initial)
  let outer := (Path.field .report .self : Path outerShape reportShape).set selected outerInitial
  let snapshot := FormSnapshot.render nestedReport outer
  check "TestWeakenedTableUsesInnerState"
    (tableRows snapshot == [["Zulu", "Bedrock", "FAIL"]])
  check "TestWeakenedSummaryUsesInnerState" (texts snapshot == ["1/2 passed"])
  let mounted : Component reportShape := .weaken filtersPath filtersComponent
  check "TestWeakenedStackRendersBothEditors"
    ((labels (FormSnapshot.render mounted selected)).contains "Only failures" &&
     (labels (FormSnapshot.render mounted selected)).contains "Provider")

private def contextualSort : Component reportShape :=
  (.visibleWhen (.project (.field .filters (.field .failuresOnly .self)))
      (.field sortPath "Contextual sort" .select))

private def testEditorBinding : IO Unit := do
  check "TestEditorReadsOuterState" ((labels (FormSnapshot.render contextualSort initial)).isEmpty)
  let enabled := (setFailuresOnly true) initial
  check "TestEditorReadsSiblingOutsideBinding"
    (labels (FormSnapshot.render contextualSort enabled) == ["Contextual sort"])

private def testProtocol : IO Unit := do
  let specification := CompositionProtocol.encode (.base reportShape) report initial
  let fixture ← IO.FS.readFile "native/tui/tests/report.json"
  let fixtureJson ← IO.ofExcept (Lean.Json.parse fixture)
  let specificationJson ← IO.ofExcept (Lean.Json.parse specification)
  check "TestReportFixtureMatchesLean" (fixtureJson == specificationJson)
  let wrapped := (Expr.weaken (.field .report .self : Path outerShape reportShape) summary).eval outerInitial
  check "TestReportQueriesWeakenIntoOuterState" (wrapped == "2/4 passed")

def run : IO Unit := do
  testFilteringAndSorting
  testRendering
  testWeakenedRendering
  testEditorBinding
  testProtocol

end Tests.Composition
