-- Compile Records.lean before checking this file:
-- mkdir -p .lake/build/lib/lean/presentation/02
-- lake env lean -o .lake/build/lib/lean/presentation/02/Records.olean presentation/02/Records.lean
import presentation.«02».Records
import Forms.Runtime.FormSnapshot

namespace Forms.Presentation

open Composition Records

inductive PersonField where
  | name
  | subscribed
  | address
  deriving DecidableEq

instance : FinEnum PersonField :=
  FinEnum.ofList [.name, .subscribed, .address] (by grind [PersonField])

def personFields : Enum where
  type := PersonField
  label
    | .name => "name"
    | .subscribed => "subscribed"
    | .address => "address"

abbrev person : DataType := .record personFields fun
  | .name => .text
  | .subscribed => .boolean
  | .address => address

def initial : ⟦person⟧
  | .name => "Ada"
  | .subscribed => false
  | .address => initialAddress

def subscribed : Path person .boolean := .field .subscribed .self
def mailingPerson : ⟦person⟧ := Path.set subscribed true initial

def wantsPostalMail : Expr person .boolean := .project subscribed

def mailingAddressForm : Component person :=
  .visibleWhen wantsPostalMail
    (.stack (some "Address") (items := addressFields) (fun
      | .street => .field (.field .address (.field .street .self)) "Street" .textInput
      | .number => .field (.field .address (.field .number .self)) "Number" .naturalInput
      | .kind => .field (.field .address (.field .kind .self)) "Kind" .select))

def personForm : Component person :=
  .stack (some "Person") (items := personFields) (fun
    | .name => .field (.field .name .self) "Name" .textInput
    | .subscribed => .field subscribed "Send me postal mail" .checkbox
    | .address => mailingAddressForm)

private def fields (component : Component person) (state : ⟦person⟧) :=
  (Runtime.FormSnapshot.render component state).fieldRefs

#guard Path.get subscribed initial == false
#guard Path.get subscribed mailingPerson == true
#guard Expr.eval wantsPostalMail initial == false
#guard Expr.eval wantsPostalMail mailingPerson == true
#guard (fields personForm initial).length == 2
#guard (fields personForm mailingPerson).length == 5
#guard (fields mailingAddressForm initial).isEmpty
#guard (fields mailingAddressForm mailingPerson).length == 3

def street : Path person .text := .field .address (.field .street .self)
def edited := Path.set street "New Street" mailingPerson
def hidden := Path.set subscribed false edited

#guard (fields personForm hidden).length == 2
#guard Path.get street hidden == "New Street"
#guard (fields personForm (Path.set subscribed true hidden)).length == 5

example : True := by
  fail_if_success have : Component person := .field street "Street" .checkbox
  fail_if_success have : Component address := mailingAddressForm
  fail_if_success have : Expr address .boolean := .project subscribed
  trivial

end Forms.Presentation
