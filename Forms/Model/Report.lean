module

public import Forms.Model.Diagnostic
public import Forms.Model.Item
public import Forms.Model.ReadOnly

@[expose] public section
namespace Forms.Model

/-- A message about server data in a raw value; it never blocks submit. -/
structure Report {α : Type} (value : α) where
  status : Diagnostic.ReportState
  severity : Diagnostic.Severity
  message : String
  targets : Targets α value

def Report.mapLocations
  {α β : Type}
  {value : α}
  {outer : β}
  (step : Location value → Location outer)
  (report : Report value)
  : Report outer where
  status := report.status
  severity := report.severity
  message := report.message
  targets := report.targets.mapLocations step

def Report.lift
  {α β : Type}
  [Fields α]
  {value : α}
  (field : Fields.Field α β)
  (report : Report (Fields.get field value))
  : Report value :=
  report.mapLocations (.field field)

def Report.inConstructor
  {α β : Type}
  [Constructors α]
  {value : β}
  (constructor : Constructors.Constructor α β)
  (report : Report value)
  : Report (Constructors.inject constructor value) :=
  report.mapLocations (.constructor constructor)

/-- The reports a type marked `@[report_rule]` makes about its own value. -/
class ReportRule (model : Type) [FormModel model] where
  reports : (raw : Raw model) → List (Report raw)

/-- Every report in a raw value. `deriving FormModel` combines the type's own rule, if it is
marked `@[report_rule]`, with the reports of its parts. -/
class Reports (model : Type) [FormModel model] where
  reports : (raw : Raw model) → List (Report raw)

instance : Reports String := ⟨fun _ => []⟩
instance : Reports Bool := ⟨fun _ => []⟩
instance : Reports Nat := ⟨fun _ => []⟩
instance : Reports Int := ⟨fun _ => []⟩
instance : Reports Int32 := ⟨fun _ => []⟩
instance : Reports Int64 := ⟨fun _ => []⟩
instance : Reports Decimal := ⟨fun _ => []⟩
instance : Reports Std.Time.PlainDate := ⟨fun _ => []⟩
instance : Reports Uuid := ⟨fun _ => []⟩
instance {α : Type} : Reports (ReadOnly α) := ⟨fun _ => []⟩

instance {α : Type} [FormModel α] [Reports α] : Reports (Option α) where
  reports
    | none => []
    | some raw => (Reports.reports (model := α) raw).map
      (Report.inConstructor (α := Option (Raw α)) OptionConstructor.some)

instance {α : Type} [FormModel α] [Reports α] [HasUuid (Raw α)] : Reports (List α) where
  reports raw := raw.attach.flatMap fun ⟨item, member⟩ =>
    (Reports.reports (model := α) item).map (Report.mapLocations (.item item member))

instance {α : Type} [FormModel α] [AlwaysValid α] : Reports { items : List α // items.Nodup } :=
  ⟨fun _ => []⟩

instance {β : Type} [FormModel β] [Reports β] : Reports (Item β) where
  reports raw :=
    (Reports.reports (model := β) raw.value).map (Report.lift (value := raw) Item.Field.value)

end Forms.Model
