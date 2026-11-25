module

import Tests.FormModel
import Tests.DerivingNames
import Tests.FinEnum
import Tests.LocalBind
import Tests.Context
import Tests.Sugar
import Tests.Actions
import Tests.Dependencies
import Tests.InputProtocol
import Tests.Wire
import Tests.ControlKeys
import Tests.FormsReact
import Tests.Invocation
import Tests.Remote
import Tests.Table
import Tests.Zoom
import Tests.TableSelection
import Tests.SharedState
import Tests.Outputs
import Tests.OutputEvaluation
import Tests.Presentation
import Tests.Rename
import Tests.Navigation
import Tests.Reports
import Tests.ServerForm
import Tests.Evidence
import Tests.Endpoints
import Tests.Lookup
import Tests.LookupCandidates
import Tests.Invalidation
import Tests.Configuration

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
  Tests.Zoom.run
  Tests.TableSelection.run
  Tests.SharedState.run
  Tests.Outputs.run
  Tests.OutputEvaluation.run
  Tests.Presentation.run
  Tests.Rename.run
  Tests.Navigation.run
  Tests.Reports.run
  Tests.ServerForm.run
  Tests.Evidence.run
  Tests.Lookup.run
  Tests.Configuration.run
  Tests.LookupCandidates.run
  Tests.Invalidation.run
