module

import Forms.Runtime.ModelProtocol
import Tests.FreshId

public section
namespace Tests.ControlKeys
open Lean Forms.Runtime Tests

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")

def run : IO Unit := do
  let examples : List (ControlKey × String) := [
    (.edit [], "[\"edit\"]"),
    (.edit [.field "items", .item firstId, .field "name"], "[\"edit\",\"items\",{\"item\":\"00000000-0000-4000-8000-000000000001\"},\"name\"]"),
    (.select [.field "shipping"], "[\"select\",\"shipping\"]"),
    (.press [0, 1] [.field "items", .item secondId], "[\"press\",[0,1],[\"items\",{\"item\":\"00000000-0000-4000-8000-000000000002\"}]]"),
    (.edit [.constructor "express", .field "phone"], "[\"edit\",{\"constructor\":\"express\"},\"phone\"]"),
    (.edit [.field "a\"b\\c"], "[\"edit\",\"a\\\"b\\\\c\"]"),
    (.tab [2] [.field "items"], "[\"tab\",[2],[\"items\"]]"),
    (.state [0, 1] [.field "items", .item secondId], "[\"state\",[0,1],[\"items\",{\"item\":\"00000000-0000-4000-8000-000000000002\"}]]")]
  for (key, encoded) in examples do
    check "Control key wire encoding changed" (ControlKeyProtocol.toString key == encoded)
    check "Control key roundtrip failed" ((ControlKeyProtocol.fromString encoded).toOption == some key)
    let event ← IO.ofExcept (ModelForm.Event.fromWire (α := Unit) (.apply encoded (toJson "21")))
    check "Event lost structured control key" (match event with
      | .apply decoded (some (.text "21")) => decoded == key
      | _ => false)
  let distinct : List ControlKey := [
    .edit [.field "0"], .edit [.item firstId], .edit [.constructor "0"],
    .select [.field "0"], .press [0] [], .press [] [.item firstId], .tab [0] [], .state [0] []]
  check "Distinct keys collided on the wire" ((distinct.map ControlKeyProtocol.toString).eraseDups.length == distinct.length)
  for malformed in ["missing", "{}", "[]", "[\"unknown\"]", "[\"edit\",true]",
      "[\"edit\",0]", "[\"edit\",{\"item\":\"nope\"}]", "[\"edit\",{}]", "[\"selectRow\"]",
      "[\"selectRow\",\"0\"]", "[\"press\",[0]]", "[\"press\",[-1],[]]",
      "[\"press\",[],[],0]", "[\"state\",[0]]", "[\"state\",[0],[],0]"] do
    check "Malformed key accepted" (!(ControlKeyProtocol.fromString malformed).isOk)
    check "Event accepted malformed key"
      (!(ModelForm.Event.fromWire (α := Unit) (.apply malformed Json.null)).isOk)
  check "Malformed item id not reported as a UUID error"
    (match ControlKeyProtocol.fromString "[\"edit\",{\"item\":\"nope\"}]" with
      | .error message => (message.splitOn "UUID").length > 1
      | .ok _ => false)
  IO.println "PASS structured control keys and protocol boundary"

end Tests.ControlKeys
