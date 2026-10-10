import Forms.ExampleForms.Invoice
import Forms.ExampleForms.Person
import Forms.ExampleForms.Thermostat
import Forms.Runtime.JsonProtocol

open Forms ExampleForms Forms.Runtime

def main (args : List String) : IO Unit :=
  IO.println (if args.contains "--invoice" then JsonProtocol.encode Invoice.invoiceType Invoice.form Invoice.draft
    else if args.contains "--thermostat" then JsonProtocol.encode Thermostat.thermostatType Thermostat.form Thermostat.draft
    else JsonProtocol.encode Person.personType Person.form Person.draft)
