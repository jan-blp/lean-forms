module

public import Mathlib.Data.String.Defs

public import Forms.Runtime.ExpressionProtocol
public import Tests.ValidationCheckers
public import Forms.ExampleForms.Person
public import Forms.ExampleForms.Invoice
public import Forms.ExampleForms.Shapes
public import Forms.ExampleForms.Location

@[expose] public section

namespace Tests.ExpressionProtocol
open Forms Forms.Runtime Forms.Runtime.ExpressionProtocol Forms.ExampleForms Lean

def check (name : String) (passed : Bool) : IO Unit :=
  unless passed do throw (IO.userError s!"FAIL {name}")

def roundTrip (emit : Json → IO Unit) {input result : DataType} (name : String)
    (expression : Forms.Expr input result) (value : ⟦input⟧) : IO Unit := do
  let schema := input.toJson
  let encoded := expression.toJson
  let argument := JsonProtocol.valueToJson value
  let actual ← IO.ofExcept (evaluate schema encoded argument)
  let expected := JsonProtocol.valueToJson (expression.eval value)
  check name (actual == expected)
  emit <| Json.mkObj [("name", toJson name), ("schema", schema), ("expression", encoded),
    ("argument", argument), ("expected", Json.mkObj [("ok", toJson true), ("value", expected)])]
  -- Check the expected result schema too, including structural record/enum equality.
  let typed := (Schema.fromJson schema).bind fun input =>
    (Schema.fromJson result.toJson).bind fun result =>
      (decode input result encoded).bind fun program =>
        (JsonProtocol.valueFromJson input.dataType argument).map fun value =>
          JsonProtocol.valueToJson (program.eval value)
  check (name ++ "TypedDecode") ((← IO.ofExcept typed) == expected)

def reject (emit : Json → IO Unit) (name : String) (schema expression value : Json) : IO Unit := do
  match evaluate schema expression value with
  | .error message =>
      check name (!message.isEmpty)
      emit <| Json.mkObj [("name", toJson name), ("schema", schema), ("expression", expression),
        ("argument", value), ("expected", Json.mkObj [("ok", toJson false), ("error", toJson message)])]
  | .ok _ => throw (IO.userError s!"FAIL {name}: accepted malformed expression")

def testOperators (emit : Json → IO Unit) : IO Unit := do
  let x : Forms.Expr .natural .natural := .project .self
  let huge := 2 ^ 256 + 123
  for value in [0, 1, 9, huge] do
    for (name, expression) in [
      ("Value", Forms.Expr.value (input := .natural) huge),
      ("Project", x), ("Add", .natAdd x (.value 7)),
      ("Sub", .natSub x (.value 10)), ("Mul", .natMul x x),
      ("If", .ifThenElse (.natLe x (.value 10)) (.value 3) x)] do
      roundTrip emit name expression value
    roundTrip emit "NatLe" (.natLe x (.value 10)) value
    roundTrip emit "NatToText" (.natToText x) value
  let text : Forms.Expr .text .text := .project .self
  roundTrip emit "TextAppend" (.textAppend (.value "Hello ") text) "κόσμε 🌍\x00!"
  roundTrip emit "TextEq" (.textEq text (.value "🌍")) "🌍"
  let boolean : Forms.Expr .boolean .boolean := .project .self
  for value in [false, true] do
    roundTrip emit "Not" (.not boolean) value
    roundTrip emit "And" (.and boolean (.value true)) value
  -- Keep the proven ISO codec compatible with the previous standard-library codec.
  for year in [1, 9, 10, 99, 100, 400, 999, 1000, 1900, 2000, 2028, 9999] do
    for month in List.range 14 do
      for day in List.range 33 do
        let text := s!"{year}".leftpad 4 '0' ++ "-" ++ s!"{month}".leftpad 2 '0' ++
          "-" ++ s!"{day}".leftpad 2 '0'
        let old := (Std.Time.PlainDate.fromLeanDateString text).toOption
        let decoded := Date.ofString? text
        check s!"DateCodecCompatibility {text}" (decoded.map (·.val) == old)
        if let some date := decoded then
          check s!"DateFormatCompatibility {text}"
            (Date.toString date == Std.Time.PlainDate.toLeanDateString date.val)
  for text in ["0000-01-01", "10000-01-01", "2028-2-29", "2028-02-029",
      "2028-02-29x", " 2028-02-29", "2028/02/29"] do
    check s!"DateCodecRejects {text}" (Date.ofString? text).isNone
  let some early := Date.ofString? "2028-02-29" | throw (IO.userError "Invalid test date")
  let some late := Date.ofString? "2028-03-01" | throw (IO.userError "Invalid test date")
  roundTrip emit "DateValue" (Forms.Expr.value (input := .date) (result := .date) early) late
  roundTrip emit "DateLe" (Forms.Expr.dateLe (.project .self) (.value late)) early

def testLists (emit : Json → IO Unit) : IO Unit := do
  let items : Forms.Expr (.list .natural) (.list .natural) := .project .self
  let x : Forms.Expr .natural .natural := .project .self
  for values in [[], [0, 9, 10, 2 ^ 128], [10, 10, 3]] do
    roundTrip emit "All" (.all items (.natLe (.value 10) (.project (.field .item .self)))) values
    roundTrip emit "Filter" (.filter items (.natLe (.value 10) x)) values
    roundTrip emit "Sum" (.sum items (.natMul x x)) values
    roundTrip emit "Length" (.length items) values
    roundTrip emit "Snoc" (.snoc items (.length items)) values
    roundTrip emit "SortNatAsc" (.sortNatBy items x false) values
    roundTrip emit "SortNatDesc" (.sortNatBy items x true) values
  for values in [[], [2, 2], [3], [0, 0], [1, 2]] do
    roundTrip emit "AllContext" Forms.Tests.ValidationCheckers.boundedItems values
    roundTrip emit "AllNested" Forms.Tests.ValidationCheckers.nestedAll values
    roundTrip emit "AllWeakened" Forms.Tests.ValidationCheckers.embeddedItems
      (fun | .outer => 99 | .item => values | .index => 99)
  let texts : Forms.Expr (.list .text) (.list .text) := .project .self
  let key : Forms.Expr .text .text := .project .self
  let values := ["beta", "ALPHA", "alpha", "Álpha", "\uE000", "𐀀", "alpha"]
  roundTrip emit "SortTextAsc" (.sortBy texts key false) values
  roundTrip emit "SortTextDesc" (.sortBy texts key true) values
  roundTrip emit "Search" (.search texts key (.value "a")) values
  roundTrip emit "ListValue" (Forms.Expr.value (input := .text) (result := .list .text) values) "unused"
  roundTrip emit "NestedLists" (Forms.Expr.sum (input := .list (.list .natural)) (.project .self)
    (.sum (.project .self) (.project .self))) [[1, 2], [], [2 ^ 100]]

def testStructured (emit : Json → IO Unit) : IO Unit := do
  roundTrip emit "RecordProject" (Forms.Expr.project Person.street) Person.draft
  roundTrip emit "RecordValue" (Forms.Expr.value (input := .natural) (result := Person.person) Person.draft) 0
  roundTrip emit "RecordBranch" (Forms.Expr.ifThenElse (input := .boolean) (.project .self)
    (.value (result := Person.person) Person.draft) (.value Person.draft)) true
  roundTrip emit "InvoiceTotal" Invoice.total Invoice.draft
  let address : Forms.Expr Person.addressKind Person.addressKind := .project .self
  for value in [.home, .work, .other] do
    roundTrip emit "EnumValue" (Forms.Expr.value (input := .natural) (result := Person.addressKind) value) 0
    roundTrip emit "EnumEq" (.enumEq address (.value .work)) value
    roundTrip emit "EnumLabel" (.enumLabel address) value
    roundTrip emit "EnumCases" (.enumCases address fun
      | .home => Forms.Expr.value 1 | .work => .value 2 | .other => .value (result := .natural) 3) value
  let area : Forms.Expr Shapes.shape .natural := .cases (.project .self) fun
    | .dot => .value 0
    | .circle => .natMul (.project .self) (.project .self)
    | .rectangle => .natMul (.project (.field .width .self)) (.project (.field .height .self))
  for value in [Shapes.draft, ⟨.dot, fun i => nomatch i⟩,
      ⟨.rectangle, fun | .width => 3 | .height => 7⟩] do
    roundTrip emit "SumCases" area value
    roundTrip emit "SumValue" (Forms.Expr.value (input := .natural) (result := Shapes.shape) value) 0
  roundTrip emit "SumOfEnums" (Forms.Expr.cases (input := Location.location) (.project .self)
    (fun | .france => .enumLabel (.project .self)
         | .japan => .enumLabel (.project .self)
         | .catalonia => .enumLabel (.project .self))) Location.draft

def testRejected (emit : Json → IO Unit) : IO Unit := do
  reject emit "UnknownOperator"
    (json% {kind: "natural"})
    (json% {kind: "wat"})
    (json% "0")
  reject emit "UnknownSchema"
    (json% {kind: "wat"})
    (json% {kind: "project", path: []})
    (json% "0")
  reject emit "ExtraFields"
    (json% {kind: "natural"})
    (json% {kind: "project", path: [], extra: true})
    (json% "0")
  reject emit "MissingField"
    (json% {kind: "natural"})
    (json% {kind: "natAdd", left: {kind: "project", path: []}})
    (json% "0")
  reject emit "WrongOperandType"
    (json% {kind: "natural"})
    (json% {kind: "natAdd", left: {kind: "project", path: []}, right: {kind: "value", type: {kind: "text"}, value: "x"}})
    (json% "0")
  reject emit "WrongLiteralValue"
    (json% {kind: "natural"})
    (json% {kind: "value", type: {kind: "natural"}, value: false})
    (json% "0")
  reject emit "ScalarPath"
    (json% {kind: "natural"})
    (json% {kind: "project", path: ["x"]})
    (json% "0")
  reject emit "NumericPath"
    (json% {kind: "natural"})
    (json% {kind: "project", path: [0]})
    (json% "0")
  reject emit "UnknownField"
    (json% {kind: "record", fields: [{name: "x", type: {kind: "natural"}}]})
    (json% {kind: "project", path: ["absent"]})
    (json% {x: "0"})
  reject emit "NonListItems"
    (json% {kind: "natural"})
    (json% {kind: "length", items: {kind: "project", path: []}})
    (json% "0")
  reject emit "WrongInputValue"
    (json% {kind: "natural"})
    (json% {kind: "project", path: []})
    (json% false)
  reject emit "MissingLiteralType"
    (json% {kind: "natural"})
    (json% {kind: "value", value: "1"})
    (json% "0")
  reject emit "DuplicateEnumLabels"
    (json% {kind: "enum", options: ["a", "a"]})
    (json% {kind: "project", path: []})
    (json% 0)
  reject emit "EnumIndexBounds"
    (json% {kind: "enum", options: ["a"]})
    (json% {kind: "project", path: []})
    (json% 1)
  reject emit "WrongEnumLabels"
    (json% {kind: "enum", options: ["a"]})
    (json% {kind: "enumLabel", subject: {kind: "project", path: []}, options: ["b"]})
    (json% 0)
  reject emit "MissingEnumBranch"
    (json% {kind: "enum", options: ["a"]})
    (json% {kind: "enumCases", type: {kind: "text"}, subject: {kind: "project", path: []}, branches: []})
    (json% 0)
  reject emit "WrongEnumBranchType"
    (json% {kind: "enum", options: ["a"]})
    (json% {kind: "enumCases", type: {kind: "text"}, subject: {kind: "project", path: []}, branches: [{kind: "value", type: {kind: "natural"}, value: "0"}]})
    (json% 0)
  reject emit "DifferentEnumDomains"
    (json% {kind: "enum", options: ["a"]})
    (json% {kind: "enumEq", left: {kind: "project", path: []}, right: {kind: "value", type: {kind: "enum", options: ["b"]}, value: 0}})
    (json% 0)
  reject emit "DuplicateRecordFields"
    (json% {kind: "record", fields: [{name: "x", type: {kind: "natural"}}, {name: "x", type: {kind: "text"}}]})
    (json% {kind: "project", path: []})
    (json% {})
  reject emit "DuplicateSumTags"
    (json% {kind: "sum", constructors: [{name: "x", type: {kind: "natural"}}, {name: "x", type: {kind: "text"}}]})
    (json% {kind: "project", path: []})
    (json% {})
  reject emit "InvalidDate"
    (json% {kind: "date"})
    (json% {kind: "project", path: []})
    (json% "2027-02-29")
  reject emit "NegativeNatural"
    (json% {kind: "natural"})
    (json% {kind: "project", path: []})
    (json% "-1")
  reject emit "WrongCondition"
    (json% {kind: "natural"})
    (json% {kind: "ifThenElse", condition: {kind: "project", path: []}, whenTrue: {kind: "value", type: {kind: "natural"}, value: "0"}, whenFalse: {kind: "value", type: {kind: "natural"}, value: "1"}})
    (json% "0")
  reject emit "DifferentBranchTypes"
    (json% {kind: "natural"})
    (json% {kind: "ifThenElse", condition: {kind: "value", type: {kind: "boolean"}, value: true}, whenTrue: {kind: "project", path: []}, whenFalse: {kind: "value", type: {kind: "text"}, value: "x"}})
    (json% "0")
  reject emit "PredicateScope"
    (json% {kind: "list", element: {kind: "natural"}})
    (json% {kind: "all", items: {kind: "project", path: []}, predicate: {kind: "project", path: ["x"]}})
    (json% [])
  reject emit "NonBooleanPredicate"
    (json% {kind: "list", element: {kind: "natural"}})
    (json% {kind: "filter", items: {kind: "project", path: []}, predicate: {kind: "project", path: []}})
    (json% [])
  reject emit "WrongSortKey"
    (json% {kind: "list", element: {kind: "natural"}})
    (json% {kind: "sortBy", items: {kind: "project", path: []}, key: {kind: "project", path: []}, descending: false})
    (json% [])
  reject emit "WrongDescending"
    (json% {kind: "list", element: {kind: "natural"}})
    (json% {kind: "sortNatBy", items: {kind: "project", path: []}, key: {kind: "project", path: []}, descending: "false"})
    (json% [])
  reject emit "WrongAppendType"
    (json% {kind: "list", element: {kind: "natural"}})
    (json% {kind: "snoc", items: {kind: "project", path: []}, value: {kind: "value", type: {kind: "text"}, value: "x"}})
    (json% [])
  reject emit "MissingSumBranch"
    (json% {kind: "sum", constructors: [{name: "one", type: {kind: "natural"}}, {name: "two", type: {kind: "text"}}]})
    (json% {kind: "cases", type: {kind: "natural"}, subject: {kind: "project", path: []}, branches: {one: {kind: "project", path: []}}})
    (json% {tag: "one", value: "0"})
  reject emit "WrongInactiveSumBranch"
    (json% {kind: "sum", constructors: [{name: "one", type: {kind: "natural"}}, {name: "two", type: {kind: "text"}}]})
    (json% {kind: "cases", type: {kind: "natural"}, subject: {kind: "project", path: []}, branches: {one: {kind: "project", path: []}, two: {kind: "project", path: []}}})
    (json% {tag: "one", value: "0"})
  reject emit "ExtraSumBranch"
    (json% {kind: "sum", constructors: [{name: "one", type: {kind: "natural"}}, {name: "two", type: {kind: "text"}}]})
    (json% {kind: "cases", type: {kind: "natural"}, subject: {kind: "project", path: []}, branches: {one: {kind: "project", path: []}, two: {kind: "value", type: {kind: "natural"}, value: "0"}, three: {kind: "value", type: {kind: "natural"}, value: "0"}}})
    (json% {tag: "one", value: "0"})
  reject emit "WrongSumTag"
    (json% {kind: "sum", constructors: [{name: "one", type: {kind: "natural"}}, {name: "two", type: {kind: "text"}}]})
    (json% {kind: "project", path: []})
    (json% {tag: "missing", value: "0"})

/-- Reuse the exact native cases as a cross-runtime test corpus. -/
def runWith (emit : Json → IO Unit) : IO Unit := do
  testOperators emit
  testLists emit
  testStructured emit
  testRejected emit

def run : IO Unit := do
  runWith (fun _ => pure ())
  IO.println "PASS: expression JSON round trips, canonical schemas, and malformed input rejection"

end Tests.ExpressionProtocol
