module

public import Forms.Model.Endpoints

@[expose] public section

open Forms.Model
namespace Tests.Endpoints

endpoints Parenthesized where
  | read : ((String → Nat)) at "/read"
  | ping : (Nat) at "/ping"

example : (Api.signature Parenthesized.read).Input = String := rfl
example : (Api.signature Parenthesized.read).Output = Nat := rfl
example : (Api.signature Parenthesized.ping).Input = Unit := rfl
example : (Api.signature Parenthesized.ping).Output = Nat := rfl

endpoints Shadowed where
  | String : String → Nat at "/string"
  | Nat : Nat → String at "/nat"

example : (Shadowed.signature Shadowed.String).Input = String := rfl
example : (Shadowed.signature Shadowed.String).Output = Nat := rfl
example : (Api.signature Shadowed.Nat).Input = Nat := rfl
example : (Api.signature Shadowed.Nat).Output = String := rfl

endpoints Nested.Shadowed where
  | String : (String → Nat) at "/nested"

example : (Api.signature Nested.Shadowed.String).Input = String := rfl
example : (Api.signature Nested.Shadowed.String).Output = Nat := rfl

/-- error: endpoints take one input; use a structure -/
#guard_msgs in
endpoints Curried where
  | read : (String → (Nat → Bool)) at "/curried"

end Tests.Endpoints
