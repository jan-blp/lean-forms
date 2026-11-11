module

public import Forms.Runtime.Web

public section
namespace Forms.Runtime.Web

theorem GetRoute.mem_all (route : GetRoute) : route ∈ all := by
  cases route <;> decide

end Forms.Runtime.Web
