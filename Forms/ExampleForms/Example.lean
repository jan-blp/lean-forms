import Forms.ExampleForms.Counter
import Forms.ExampleForms.Counters
import Forms.ExampleForms.Person
import Forms.ExampleForms.Booking
import Forms.ExampleForms.Basket
import Forms.ExampleForms.TestReport
import Forms.ExampleForms.Location
import Forms.ExampleForms.Shapes
import Forms.ExampleForms.Invoice
import Forms.ExampleForms.Thermostat

namespace Forms.ExampleForms

inductive Example where
  | counter
  | counters
  | person
  | booking
  | basket
  | report
  | location
  | shapes
  | invoice
  | thermostat
  deriving DecidableEq

instance : FinEnum Example :=
  FinEnum.ofList [.person, .counter, .counters, .booking, .basket, .report,
    .location, .shapes, .invoice, .thermostat]
    (by intro selected; cases selected <;> simp)

def Example.name : Example → String
  | .counter => "counter"
  | .counters => "counters"
  | .person => "person"
  | .booking => "booking"
  | .basket => "basket"
  | .report => "report"
  | .location => "location"
  | .shapes => "shapes"
  | .invoice => "invoice"
  | .thermostat => "thermostat"

theorem Example.name_injective : Function.Injective Example.name := by
  intro a b h
  cases a <;> cases b <;> simp_all [Example.name]

def Example.names : List String :=
  (FinEnum.toList Example).map Example.name

def Example.ofName (name : String) : Option Example :=
  (FinEnum.toList Example).find? (fun selected => selected.name == name)

structure Example.Definition where
  {ty : DataType}
  refined : RefinedDataType ty
  component : Composition.Component ty
  initial : ⟦ty⟧

def Example.definition : Example → Example.Definition
  | .counter => {
      refined := .base .natural
      component := Counter.form
      initial := 0
    }
  | .counters => {
      refined := .base Counters.state
      component := Counters.form
      initial := Counters.initial
    }
  | .person => {
      refined := Person.personType
      component := Person.form
      initial := Person.draft
    }
  | .booking => {
      refined := Booking.bookingType
      component := Booking.form
      initial := Booking.draft
    }
  | .basket => {
      refined := .base Basket.basket
      component := Basket.basketView
      initial := Basket.initial
    }
  | .report => {
      refined := .base TestReport.reportShape
      component := TestReport.report
      initial := TestReport.initial
    }
  | .location => {
      refined := Location.locationType
      component := Location.form
      initial := Location.draft
    }
  | .shapes => {
      refined := Shapes.shapeType
      component := Shapes.form
      initial := Shapes.draft
    }
  | .invoice => {
      refined := Invoice.invoiceType
      component := Invoice.form
      initial := Invoice.draft
    }
  | .thermostat => {
      refined := Thermostat.thermostatType
      component := Thermostat.form
      initial := Thermostat.draft
    }

end Forms.ExampleForms
