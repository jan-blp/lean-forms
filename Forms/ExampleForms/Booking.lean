import Forms.Core.Component.Builder
import Forms.Core.RefinedDataType

namespace Forms.ExampleForms.Booking
open Composition

inductive Field where
  | startDate | endDate
  deriving DecidableEq, Repr

instance : FinEnum Field :=
  FinEnum.ofList [.startDate, .endDate] (by grind [Field])

def fields : Enum where
  type := Field
  label
    | .startDate => "startDate"
    | .endDate => "endDate"

abbrev booking : DataType := .record fields (fun _ => .date)

def startDate : Path booking .date := .field .startDate .self
def endDate : Path booking .date := .field .endDate .self

def bookingDate : RefinedDataType .date :=
  .dateRange ⟨⟨2028, 1, 1, by decide⟩, by decide⟩ ⟨⟨2028, 12, 31, by decide⟩, by decide⟩

def bookingType : RefinedDataType booking :=
  .refine (.record fun _ => bookingDate)
    { condition := .dateLe (.project startDate) (.project endDate)
      errorMessage := "End date must be on or after start date."
      errorLocation := some ⟨endDate⟩ }

def initial : RefinedDataType.ValidatedValue bookingType :=
  ⟨(fun
    | .startDate => ⟨⟨⟨2028, 2, 28, by decide⟩, by decide⟩, by decide⟩
    | .endDate => ⟨⟨⟨2028, 3, 1, by decide⟩, by decide⟩, by decide⟩), by decide⟩

def draft : ⟦booking⟧ := RefinedDataType.erase bookingType initial

def form : Component booking :=
  (show Component.Builder booking booking from
    Component.Builder.group "Booking" fun
      | .startDate => Component.Builder.field "Start date (YYYY-MM-DD)" .dateInput
      | .endDate => Component.Builder.field "End date (YYYY-MM-DD)" .dateInput) .self

end Forms.ExampleForms.Booking
