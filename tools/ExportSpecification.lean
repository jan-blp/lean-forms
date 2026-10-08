import Forms.ExampleForms.Person
import Forms.Technology.Specification

def main : IO Unit :=
  IO.println (Forms.Technology.Specification.encode
    Forms.ExampleForms.Person.form Forms.ExampleForms.Person.initial)
