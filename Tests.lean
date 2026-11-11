module

import Tests.FormModel
import Tests.Dependencies
import Tests.InputProtocol
import Tests.Wire
import Tests.FormsReact
import Tests.Invocation
import Tests.Remote
import Tests.Table

meta import Forms.Model.Computation.Theorems
meta import Forms.Runtime.ModelView.Theorems

public def main : IO Unit := do
  Tests.FormModel.run
  Tests.Dependencies.run
  Tests.InputProtocol.run
  Tests.Wire.run
  Tests.FormsReact.run
  Tests.Invocation.run
  Tests.Remote.run
  Tests.Table.run
