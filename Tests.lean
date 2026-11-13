module

import Tests.FormModel
import Tests.LocalBind
import Tests.Context
import Tests.Actions
import Tests.Dependencies
import Tests.InputProtocol
import Tests.Wire
import Tests.ControlKeys
import Tests.FormsReact
import Tests.Invocation
import Tests.Remote
import Tests.Table
import Tests.Focus
import Tests.TableSelection
import Tests.SharedState
import Tests.Outputs
import Tests.OutputEvaluation

meta import Forms.Model.Computation.Theorems
meta import Forms.Runtime.ModelView.Theorems

public def main : IO Unit := do
  Tests.FormModel.run
  Tests.LocalBind.run
  Tests.Context.run
  Tests.Actions.run
  Tests.Dependencies.run
  Tests.InputProtocol.run
  Tests.Wire.run
  Tests.ControlKeys.run
  Tests.FormsReact.run
  Tests.Invocation.run
  Tests.Remote.run
  Tests.Table.run
  Tests.Focus.run
  Tests.TableSelection.run
  Tests.SharedState.run
  Tests.Outputs.run
  Tests.OutputEvaluation.run
