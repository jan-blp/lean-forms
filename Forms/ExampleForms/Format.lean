module

@[expose] public section
namespace Forms.ExampleForms

/-- Swiss thousands separators, e.g. `12'345`. -/
def swiss (n : Nat) : String :=
  if n < 1000 then toString n
  else
    let rest := n % 1000
    let pad := if rest < 10 then "00" else if rest < 100 then "0" else ""
    swiss (n / 1000) ++ "'" ++ pad ++ toString rest
termination_by n
decreasing_by omega

end Forms.ExampleForms
