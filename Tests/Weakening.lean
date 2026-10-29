import Forms.ExampleForms.Basket
import Forms.ExampleForms.TestReport
import Forms.ExampleForms.Person
import Forms.ExampleForms.Invoice
import Forms.ExampleForms.Location
import Forms.ExampleForms.Thermostat
import Forms.Runtime.CompositionProtocol
import Forms.Runtime.FormSnapshot

namespace Tests.Weakening
open Forms Forms.Composition Forms.Runtime Forms.ExampleForms

inductive HostField where
  | content
  | title
  deriving DecidableEq

instance : FinEnum HostField := FinEnum.ofList [.content, .title] (by grind [HostField])

def hostFields : Enum where
  type := HostField
  label
    | .content => "content"
    | .title => "title"

abbrev host (inner : DataType) : DataType := .record hostFields fun
  | .content => inner
  | .title => .text

def contentPath (inner : DataType) : Path (host inner) inner := .field .content .self

def wrap {inner : DataType} (value : ⟦inner⟧) : ⟦host inner⟧
  | .content => value
  | .title => "Keep this title"

def reportSpec : String :=
  CompositionProtocol.encode (.base (host TestReport.reportShape))
    (TestReport.report.weaken (contentPath _)) (wrap TestReport.initial)

def basketSpec : String :=
  CompositionProtocol.encode (.base (host Basket.basket))
    (Basket.basketView.weaken (contentPath _)) (wrap Basket.initial)

private def check (name : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError ("FAIL " ++ name))
  IO.println ("PASS " ++ name)

private def signature (fields : List FieldRef) := fields.map fun field =>
  (field.labels, field.indices, field.disabled, match field.content with
    | .input widget => Widget.name widget
    | .computed value => (JsonProtocol.valueToJson value).compress)

private def checkForm {state : DataType} (name : String)
    (form : Component state) (value : ⟦state⟧) : IO Unit := do
  let original := (FormSnapshot.render form value).fieldRefs
  let mounted := (FormSnapshot.render (form.weaken (contentPath state)) (wrap value)).fieldRefs
  check name (signature (mounted.map fun field => { field with indices := field.indices.drop 1 }) ==
    signature original)

private def checkComponent {state : DataType} (component : Component state) : IO Unit := do
  check "WeakenSelfPreservesComponent" (CompositionProtocol.componentToJson (component.weaken .self) ==
    CompositionProtocol.componentToJson component)
  let inner := contentPath state
  let outer := contentPath (host state)
  check "WeakenComposesPaths"
    (CompositionProtocol.componentToJson ((component.weaken inner).weaken outer) ==
     CompositionProtocol.componentToJson (component.weaken (outer.trans inner)))

def run : IO Unit := do
  checkComponent Basket.basketView
  checkComponent TestReport.report
  checkForm "WeakenGroupsAndVisibility" Person.form Person.draft
  checkForm "WeakenListKeepsItemContext" Invoice.form Invoice.draft
  checkForm "WeakenSumKeepsPayloadContext" Location.form Location.draft
  checkForm "WeakenDisabling" Thermostat.form Thermostat.draft
  -- Force context-dependent wrappers to read a sibling of the edited value.
  let form : Component TestReport.reportShape :=
    .disabledWhen (.project (.field .filters (.field .failuresOnly .self)))
      (.visibleWhen (.not (.project (.field .filters (.field .failuresOnly .self))))
        (.field TestReport.sortPath "Sort" .select))
  checkForm "WeakenContextOutsideEditorTarget" form TestReport.initial
  for (name, exported) in [("weakened-report", reportSpec), ("weakened-basket", basketSpec)] do
    let actual ← IO.ofExcept (Lean.Json.parse exported)
    let expected ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile s!"native/tui/tests/{name}.json"))
    check (name ++ " fixture") (actual == expected)

end Tests.Weakening
