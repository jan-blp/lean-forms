module

import Forms.Runtime.ModelProtocol

public section
namespace Tests.ControlKeys
open Lean Forms.Runtime

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")

def run : IO Unit := do
  let examples : List (ControlKey × String) := [
    (.edit [], "[\"edit\"]"),
    (.edit [.field "items", .index 0, .field "name"], "[\"edit\",\"items\",0,\"name\"]"),
    (.select [.field "shipping"], "[\"select\",\"shipping\"]"),
    (.add [.field "items"], "[\"add\",\"items\"]"),
    (.remove [.field "items", .index 1], "[\"remove\",\"items\",1]"),
    (.selectRow [] 2, "[\"selectRow\",2]"),
    (.selectRow [1, 0] 2, "[\"selectRow\",1,0,2]"),
    (.press [0, 1] [.field "items", .index 2], "[\"press\",[0,1],[\"items\",2]]"),
    (.edit [.constructor "express", .field "phone"], "[\"edit\",{\"constructor\":\"express\"},\"phone\"]"),
    (.edit [.field "a\"b\\c"], "[\"edit\",\"a\\\"b\\\\c\"]")]
  for (key, encoded) in examples do
    check "Control key wire encoding changed" (ControlKeyProtocol.toString key == encoded)
    check "Control key roundtrip failed" ((ControlKeyProtocol.fromString encoded).toOption == some key)
    let event ← IO.ofExcept (ModelForm.Event.fromWire (.apply encoded (toJson "21")))
    check "Event lost structured control key" (match event with
      | .apply decoded (some (.text "21")) => decoded == key
      | _ => false)
  let distinct : List ControlKey := [
    .edit [.field "0"], .edit [.index 0], .edit [.constructor "0"],
    .select [.field "0"], .press [0] [], .press [] [.index 0]]
  check "Distinct keys collided on the wire" ((distinct.map ControlKeyProtocol.toString).eraseDups.length == distinct.length)
  for malformed in ["missing", "{}", "[]", "[\"unknown\"]", "[\"edit\",true]",
      "[\"edit\",-1]", "[\"edit\",1.5]", "[\"edit\",{}]", "[\"selectRow\"]",
      "[\"selectRow\",\"0\"]", "[\"press\",[0]]", "[\"press\",[-1],[]]",
      "[\"press\",[],[],0]"] do
    check "Malformed key accepted" (!(ControlKeyProtocol.fromString malformed).isOk)
    check "Event accepted malformed key" (!(ModelForm.Event.fromWire (.apply malformed Json.null)).isOk)
  IO.println "PASS structured control keys and protocol boundary"

end Tests.ControlKeys
