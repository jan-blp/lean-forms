module

public import Forms.ExampleForms.Registry
public import Tests.FreshId
public meta import Forms.Deriving.FinEnum

public section
namespace Tests.Configuration
open Lean Forms.Model Forms.Runtime Forms.ExampleForms

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"

theorem excluding_nothing (diagnostic : Diagnostic) : diagnostic.excluding [] = some diagnostic := by
  obtain ⟨kind, message, targets⟩ := diagnostic
  cases targets <;> simp [Diagnostic.excluding, List.find?]

private def excludedCity : List ExcludedField :=
  [{ scope := [.field "city"], label := "City" }]

private def error (message : String) (targets : Diagnostic.Targets) : Diagnostic :=
  { kind := .error, message, targets }

private def capabilities : TenantInvoice.FieldKey → Capabilities :=
  (TenantInvoice.form (Γ := [])).capabilities

private def supplier : Slot [] TenantInvoice.Raw TenantInvoice.FieldKey :=
  .field .supplier .text .forbidden (lockable := false)

/-- A key used twice, and keys left unused, are rejected when the form is registered. -/
example : ¬ (Configured.group (Γ := []) "Twice" [supplier, supplier]).WellKeyed := by
  decide

example : ¬ (Configured.group (Γ := []) "Partial" [supplier]).WellKeyed := by
  decide

private inductive Overlapping where
  | address
  | city
  deriving DecidableEq, FinEnum

/-- Keys whose fields overlap are rejected when their paths are declared. -/
example : ¬ PrefixFree fun
    | Overlapping.address => [.field "address"]
    | Overlapping.city => [.field "address", .field "city"] := by
  decide

example : (TenantInvoice.form (Γ := [])).WellKeyed := by
  decide

private def opened
  (settings : Settings)
  (value : Json := tenantInvoice.definition.initial)
  : IO (OpenedForm tenantInvoice.definition.State tenantInvoice.definition.Raw) :=
  IO.ofExcept (tenantInvoice.definition.openState value settings supply)

private def shown (snapshot : ModelForm.Snapshot tenantInvoice.definition.Raw) : List String :=
  snapshot.controls.map (·.label)

private def disabled (snapshot : ModelForm.Snapshot tenantInvoice.definition.Raw) : List String :=
  (snapshot.controls.filter (·.disabled)).map (·.label)

def run : IO Unit := do
  check "ExcludedErrorBecomesGlobal"
    (Diagnostic.excluding excludedCity
      (error "Required." (.locations [.field "city", .field "name"] [])) ==
      some (error "City: Required." .global))
  check "ExcludedErrorKeepsShownLocations"
    (Diagnostic.excluding excludedCity
      (error "Mismatch." (.locations [.field "city"] [[.field "zip"]])) ==
      some (error "Mismatch." (.locations [.field "zip"] [])))
  check "ExcludedReportIsDropped"
    (Diagnostic.excluding excludedCity
      { kind := .report { state := .unresolved, severity := .warning, outdated := false }
        message := "Unknown city."
        targets := .locations [.field "city"] [] } == none)
  check "SettingsWarnAboutUnusableEntries"
    ((Settings.resolve { fields := [
      { key := "supplier", state := .excluded },
      { key := "postingDate", state := .readOnly },
      { key := "reference", state := .readOnly },
      { key := "reference", state := .shown },
      { key := "missing", state := .shown }] } capabilities).2 == [
      "Field \"supplier\" cannot be excluded; it is shown.",
      "Field \"postingDate\" cannot be read-only; it is shown.",
      "Field \"reference\" appears twice in the settings.",
      "Unknown field \"missing\" in the settings."])
  let defaults ← opened .empty
  check "ConfiguredDefaultsShowFieldsInAuthorOrder"
    (shown defaults.snapshot ==
      ["Invoice number", "Supplier", "Reference", "VAT date", "Street", "City"] &&
      (disabled defaults.snapshot).isEmpty && defaults.warnings.isEmpty)
  let tenant ← opened TenantInvoice.tenantSettings
  check "ConfiguredTenantReordersExcludesAndLocks"
    (shown tenant.snapshot == ["Invoice number", "Posting date", "Supplier", "Street"] &&
      disabled tenant.snapshot == ["Supplier"])
  check "ConfiguredTenantWarnsAboutUnknownKeys"
    (tenant.warnings == ["Unknown field \"legacyField\" in the settings."])
  let value := letI := tenantInvoice.definition.encode; toJson tenant.snapshot.value
  check "ConfiguredResetAppliesFallbacks"
    (value.getObjValD "vatDate" == Json.null &&
      (value.getObjValD "address").getObjValD "city" == toJson "" &&
      value.getObjValD "reference" == toJson "PO-7")
  let blank ← opened TenantInvoice.tenantSettings
    (tenantInvoice.definition.initial.setObjVal! "reference" (toJson ""))
  let (_, submitted) ← IO.ofExcept (tenantInvoice.definition.execute blank.state .submit)
  check "ConfiguredExcludedErrorsNameTheField"
    (submitted.ui.status == "Reference: Enter the reference." && submitted.ui.error &&
      submitted.effects.isEmpty)

end Tests.Configuration
