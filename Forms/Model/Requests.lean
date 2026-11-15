module

public import Forms.Runtime.ModelView

@[expose] public section
namespace Forms.Model

def Component.requests
  {Γ : Context}
  {α β : Type}
  (component : Component Γ α β)
  (cache : HttpRequest.Cache)
  (value : α)
  (env : Env Γ)
  (locals : component.LocalState := component.initialState)
  : List HttpRequest :=
  (component.evaluate value env cache locals).requests

end Forms.Model
