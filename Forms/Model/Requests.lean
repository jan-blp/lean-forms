module

public import Forms.Runtime.ModelView

@[expose] public section
namespace Forms.Model

def Component.requests
  {Γ : Context}
  {α β : Type}
  (component : Component Γ α β)
  (fetchState : Runtime.FetchState)
  (value : α)
  (env : Env Γ)
  (locals : component.LocalState := component.initialState)
  : List HttpRequest :=
  (component.evaluate value env fetchState locals).requests

end Forms.Model
