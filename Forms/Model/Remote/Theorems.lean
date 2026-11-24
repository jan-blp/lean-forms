module

public import Forms.Model.Remote

public section
namespace Forms.Model

theorem Api.scope_contains_request
  {endpoint : Type}
  [FinEnum endpoint]
  [Api endpoint]
  (named : endpoint)
  (input : (Api.signature named).Input)
  : (Api.scope named).contains (Api.request named input) = true := by
  simp [Api.scope, Api.request, RequestScope.contains]
  rfl

end Forms.Model
