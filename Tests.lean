module

import Tests.FormModel
import Tests.Dependencies
import Tests.InputProtocol
import Tests.Wire
import Tests.FormsReact

public def main : IO Unit := do
  Tests.FormModel.run
  Tests.Dependencies.run
  Tests.InputProtocol.run
  Tests.Wire.run
  Tests.FormsReact.run
