import Forms.Core.Composition
import Forms.Core.ActionHistory

namespace Forms.ExampleForms.Counter

open Composition

def plusOne : WidgetAction .natural :=
  ⟨"+1", .button (.natAdd (.project .self) (.value 1))⟩
def plusFive : WidgetAction .natural :=
  ⟨"+5", .button (.natAdd (.project .self) (.value 5))⟩
def replace : WidgetAction .natural :=
  ⟨"Value", .editor .naturalInput (.project (.field .argument .self))⟩
def minusOne : WidgetAction .natural :=
  ⟨"−1", .button (.natSub (.project .self) (.value 1))⟩

inductive CounterAction where
  | plusOne
  | plusFive
  | replace
  | minusOne
  deriving DecidableEq, BEq

instance : FinEnum CounterAction :=
  FinEnum.ofList [.plusOne, .plusFive, .replace, .minusOne] (by grind [CounterAction])

def actionIds : Enum where
  type := CounterAction
  label
    | .plusOne => "plusOne"
    | .plusFive => "plusFive"
    | .replace => "replace"
    | .minusOne => "minusOne"

def actions : CounterAction → WidgetAction .natural
  | .plusOne => plusOne
  | .plusFive => plusFive
  | .replace => replace
  | .minusOne => minusOne

def mkNatWidget {ids : Enum} (definitions : ids → WidgetAction .natural) : Component .natural :=
  .actionWidget .self "Counter" definitions

def form : Component .natural := mkNatWidget (ids := actionIds) actions

def replayActions (id : CounterAction) : ActionPresentation .natural :=
  (actions id).presentation

def click (history : ActionHistory .natural CounterAction) (id : CounterAction)
    : Except String (ActionHistory .natural CounterAction) :=
  history.apply replayActions (.button id)

end Forms.ExampleForms.Counter
