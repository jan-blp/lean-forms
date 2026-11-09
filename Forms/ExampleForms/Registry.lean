module

public import Forms.Runtime.PersonProtocol
public import Std.Data.HashMap

@[expose] public section
namespace Forms.ExampleForms

/-- Forms available in the example application, shared by its native and Wasm builds. -/
def registeredForms : Std.HashMap String Runtime.RegisteredForm :=
  ({} : Std.HashMap String Runtime.RegisteredForm).insert Runtime.PersonProtocol.name
    { definition := Runtime.PersonProtocol.formDefinition, submitUrl := "/api/submit" }

end Forms.ExampleForms
