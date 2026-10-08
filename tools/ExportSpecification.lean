import Forms.ExampleForms.Person
import Forms.Runtime.JsonProtocol

def main : IO Unit :=
  IO.println (Forms.Runtime.JsonProtocol.encode
    Forms.ExampleForms.Person.form Forms.ExampleForms.Person.initial)
