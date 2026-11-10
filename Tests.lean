module

import Tests.FormModel
import Tests.Dependencies
import Tests.InputProtocol
import Tests.Wire
import Tests.FormsReact
import Tests.Invocation
import Tests.Remote

public def main : IO Unit := do
  Tests.FormModel.run
  Tests.Dependencies.run
  Tests.InputProtocol.run
  Tests.Wire.run
  Tests.FormsReact.run
  Tests.Invocation.run
  Tests.Remote.run
