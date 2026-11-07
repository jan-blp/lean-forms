module

public import Forms.ExampleForms.Basket
public import Forms.ExampleForms.TestReport
public import Forms.ExampleForms.Person
public import Forms.ExampleForms.Invoice
public import Forms.ExampleForms.Location
public import Forms.ExampleForms.Thermostat
public import Forms.Runtime.CompiledView
public import Forms.Runtime.JsonProtocol
public import Tests.FormSnapshot

@[expose] public section

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

def check (name : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError ("FAIL " ++ name))
  IO.println ("PASS " ++ name)

def signature (fields : List FieldRef) := fields.map fun field =>
  (field.labels, field.indices, field.disabled, match field.content with
    | .input widget => Widget.name widget
    | .computed value => (JsonProtocol.valueToJson value).compress)

def checkForm {state : DataType} (name : String)
    (form : Component state) (value : ⟦state⟧) : IO Unit := do
  let original := (FormSnapshot.render form value).fieldRefs
  let mounted := (FormSnapshot.render (form.weaken (contentPath state)) (wrap value)).fieldRefs
  check name (signature (mounted.map fun field => { field with indices := field.indices.drop 1 }) ==
    signature original)

def checkComponent {state : DataType} (component : Component state) (value : ⟦state⟧) : IO Unit := do
  check "WeakenSelfPreservesView" ((CompiledView.render (component.weaken .self) value).view ==
    (CompiledView.render component value).view)
  let inner := contentPath state
  let outer := contentPath (host state)
  check "WeakenComposesPaths"
    ((CompiledView.render ((component.weaken inner).weaken outer) (wrap (wrap value))).view ==
     (CompiledView.render (component.weaken (outer.trans inner)) (wrap (wrap value))).view)

def run : IO Unit := do
  checkComponent Basket.basketView Basket.initial
  checkComponent TestReport.report TestReport.initial
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

end Tests.Weakening
