import Forms.ExampleForms.Shapes
import Forms.ExampleForms.Location
import Forms.ExampleForms.Invoice
import Forms.ExampleForms.Person
import Forms.Runtime.JsonProtocol

open Forms ExampleForms Forms.Runtime

def main (args : List String) : IO Unit :=
  IO.println (if args.contains "shapes" then JsonProtocol.encode Shapes.form Shapes.initial
    else if args.contains "location" then JsonProtocol.encode Location.form Location.initial
    else if args.contains "invoice" then JsonProtocol.encode Invoice.form Invoice.initial
    else JsonProtocol.encode Person.form Person.initial)
