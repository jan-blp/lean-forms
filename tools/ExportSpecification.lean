import Forms.ExampleForms.Booking
import Forms.ExampleForms.Location
import Forms.ExampleForms.Shapes
import Forms.ExampleForms.Invoice
import Forms.ExampleForms.Person
import Forms.ExampleForms.Thermostat
import Forms.Runtime.CompositionProtocol

open Forms ExampleForms Forms.Runtime

def main (args : List String) : IO Unit :=
  IO.println (if args.contains "booking" then CompositionProtocol.encode Booking.bookingType Booking.form Booking.draft
    else if args.contains "location" then CompositionProtocol.encode Location.locationType Location.form Location.draft
    else if args.contains "shapes" then CompositionProtocol.encode Shapes.shapeType Shapes.form Shapes.draft
    else if args.contains "invoice" then CompositionProtocol.encode Invoice.invoiceType Invoice.form Invoice.draft
    else if args.contains "thermostat" then CompositionProtocol.encode Thermostat.thermostatType Thermostat.form Thermostat.draft
    else CompositionProtocol.encode Person.personType Person.form Person.draft)
