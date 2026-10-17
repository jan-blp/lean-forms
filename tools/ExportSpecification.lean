import Forms.ExampleForms.Location
import Forms.ExampleForms.Booking
import Forms.ExampleForms.Shapes
import Forms.ExampleForms.Invoice
import Forms.ExampleForms.Person
import Forms.ExampleForms.Thermostat
import Forms.Runtime.JsonProtocol

open Forms ExampleForms Forms.Runtime

def main (args : List String) : IO Unit :=
  IO.println (if args.contains "location" then JsonProtocol.encode Location.locationType Location.form Location.draft
    else if args.contains "booking" then JsonProtocol.encode Booking.bookingType Booking.form Booking.draft
    else if args.contains "shapes" then JsonProtocol.encode Shapes.shapeType Shapes.form Shapes.draft
    else if args.contains "invoice" then JsonProtocol.encode Invoice.invoiceType Invoice.form Invoice.draft
    else if args.contains "thermostat" then JsonProtocol.encode Thermostat.thermostatType Thermostat.form Thermostat.draft
    else JsonProtocol.encode Person.personType Person.form Person.draft)
