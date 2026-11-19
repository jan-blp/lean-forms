module

import Forms.Model.Sugar

open Forms.Model Forms.Model.Sugar

set_option pp.mvars false

private def directImport : Component [] Nat Nat := named%
  state% count := (1 : Nat);
  .output { inputs := inputs[.ui ref[count]], run := id }

example : directImport = .bind (1 : Nat) (.output { inputs := inputs[.ui .here], run := id }) := rfl

/-- error: Name '_shared' is already in scope; choose a different name -/
#guard_msgs in
example {Γ : Context} (_shared : Var Γ Nat) : Component Γ Nat := named%[_shared, _shared]
  .computed "Shared" { inputs := inputs[.ui ref[_shared]], run := toString }

/-- error: Name '_shared' is already in scope; choose a different name -/
#guard_msgs in
example {Γ : Context} (_shared : Var Γ Nat) : Component Γ Nat := named%[_shared]
  state% _shared := (0 : Nat);
  .computed "Shared" { inputs := inputs[.ui ref[_shared]], run := toString }

/-- error: Name 'count' is already in scope; choose a different name -/
#guard_msgs in
example : Component [] Nat Nat := named%
  state% count := (10 : Nat);
  state% count := (20 : Nat);
  .output { inputs := inputs[.ui ref[count]], run := id }

/-- error: Name 'count' is already in scope; choose a different name -/
#guard_msgs in
example : Component [] Nat := named%
  present%
    own% count := .computed "First" "1";
    own% count := .computed "Second" "2";
    .arrange (.const (.place slot[count]))

/-- error: Name 'count' is already in scope; choose a different name -/
#guard_msgs in
example : Component [] Nat := named%
  present%
    state% count := (0 : Nat);
    own% count := .computed "Count" "1";
    .arrange (.const (.place slot[count]))

/-- error: Name 'count' is already in scope; choose a different name -/
#guard_msgs in
example : Component [] Nat Nat := named%
  state% count := (10 : Nat);
  alias% count := count;
  .output { inputs := inputs[.ui ref[count]], run := id }

/-- error: Name 'other' is already in scope; choose a different name -/
#guard_msgs in
example : Component [] Nat Nat := named%
  state% count := (10 : Nat);
  alias% other := count;
  state% other := (20 : Nat);
  .output { inputs := inputs[.ui ref[other]], run := id }

/-- error: Name 'active' is already in scope; choose a different name -/
#guard_msgs in
example : Component [] Nat := named%
  present%
    tabs% active, active := "Tabs", #v["One", "Two"];
    .arrange (.const (.place slot[active]))

/-- error: Name 'current' is already in scope; choose a different name -/
#guard_msgs in
example : Computation (Context.row Nat []) Nat String := named%
  row% current, current => {
    inputs := inputs[.ui ref[current]]
    run := fun row => toString row.current }

/--
error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  ℕ
in the application
  Computation.const true
-/
#guard_msgs in
example : Component [] Nat := named%
  state% number := (1 : Nat);
  .button "Wrong type" (.set ref[number] (.const true))

/--
error: Application type mismatch: The argument
  counter✝¹
has type
  InputRef [{ access := Access.readOnly, type := ℕ }] ℕ
but is expected to have type
  Var [{ access := Access.readOnly, type := ℕ }] ?_
in the application
  Action.set counter✝¹
-/
#guard_msgs in
example : Component [] Nat := named%
  present%
    own% counter := .output (.const (0 : Nat));
    own% button := .button "Write read-only output" (.set ref[counter] (.const 1));
    .arrange (.const (.place slot[button]))

/-- error: Use state% for bindings inside named% -/
#guard_msgs in
example : Component [] Nat Nat := named%
  state% outer := (10 : Nat);
  .bind (20 : Nat) (.output { inputs := inputs[.ui ref[outer]], run := id })

/-- error: Use own% for ownership inside named% -/
#guard_msgs in
example : Component [] Nat := named%
  present%
    .own (.computed "Raw" "binding") (.arrange (.const (.place .here)))

/-- error: Unknown variable 'later' in this scope -/
#guard_msgs in
example : Component [] Nat Nat := named%
  .output { inputs := inputs[.ui ref[later]], run := id }

/-- error: Unknown variable 'self' in this scope -/
#guard_msgs in
example : Component [] Nat := named%
  present%
    own% self := .computed "Self" { inputs := inputs[.ui ref[self]], run := id };
    .arrange (.const (.place slot[self]))

/-- error: Unknown variable 'outer' in this scope -/
#guard_msgs in
example : Component [] Nat Nat := named%
  state% outer := (10 : Nat);
  let independent : Component [] Nat Nat := named%
    state% inner := (20 : Nat);
    .output { inputs := inputs[.ui ref[outer]], run := id }
  independent.weaken

/-- error: Unknown slot 'outer' in this scope -/
#guard_msgs in
example : Component [] Nat := named%
  present%
    own% outer := .computed "Outer" "outside";
    own% nested := present%
      own% inner := .computed "Inner" "inside";
      .arrange (.const (.place slot[outer]));
    .arrange (.const (.place slot[nested]))

/-- error: ref[...] is only valid inside named% -/
#guard_msgs in
example : Var [] Nat := ref[x]

/-- error: slot[...] is only valid inside named% -/
#guard_msgs in
example : Slot [] 0 := slot[x]

/-- error: state% is only valid inside named% -/
#guard_msgs in
example : Component [] Nat := state% x := (0 : Nat); .computed "X" "0"

/-- error: own% is only valid inside named% -/
#guard_msgs in
example : Component [] Nat := own% x := .computed "X" "0"; .computed "X" "0"

/-- error: present% is only valid inside named% -/
#guard_msgs in
example : Component [] Nat := present% .arrange (.const (.group none []))

/-- error: tabs% is only valid inside named% -/
#guard_msgs in
example : Component [] Nat := tabs% active, strip := "Tabs", #v["One"]; .computed "X" "0"

/-- error: alias% is only valid inside named% -/
#guard_msgs in
example : Component [] Nat := alias% x := y; .computed "X" "0"

/-- error: row% is only valid inside named% -/
#guard_msgs in
example : Computation (Context.row Nat []) Nat String := row% current, removed => (.const "row")

/-- error: own% requires a presentation; use present% -/
#guard_msgs in
example : Component [] Nat := named%
  own% x := .computed "X" "0";
  .arrange (.const (.place slot[x]))

/-- error: tabs% requires a presentation; use present% -/
#guard_msgs in
example : Component [] Nat := named%
  tabs% active, strip := "Tabs", #v["One"];
  .arrange (.const (.place slot[strip]))

/-- error: Unknown variable 'missing' in this scope -/
#guard_msgs in
example : Component [] Nat := named% alias% x := missing; .computed "X" "0"

/-- error: Use the named% binding syntax here -/
#guard_msgs in
example : Component [] Nat := named% Component.bind (0 : Nat) (.computed "X" "0")

/-- error: Use present% for presentations inside named% -/
#guard_msgs in
example : Component [] Nat := named% .present (.arrange (.const (.group none [])))

/-- error: Use the named% binding syntax here -/
#guard_msgs in
example : Component [] Nat := named%
  present% Presentation.tabs "Tabs" #v["One"] (.arrange (.const (.group none [])))

/--
@ +4:31...37
error: Application type mismatch: The argument
  shared✝
has type
  Var [{ access := Access.writable, type := ℕ }] ℕ
but is expected to have type
  Ref (Context.row (Item ℕ) [{ access := Access.writable, type := ℕ }]) (?_ shared✝) (?_ shared✝)
in the application
  Inputs.ui shared✝
-/
#guard_msgs (positions := true) in
example : Component [] (List (Item Nat)) (List Unit) := named%
  state% shared := (0 : Nat);
  .list .self "Rows"
    { inputs := inputs[.ui ref[shared]], run := toString }
    "Add" (Item.mkWithoutUuid 0) (.computed "Row" "value")

/--
@ +5:31...37
error: Application type mismatch: The argument
  shared✝
has type
  Var [{ access := Access.writable, type := ℕ }] ℕ
but is expected to have type
  Member { access := ?_ shared✝ ignored✝, type := ?_ shared✝ ignored✝ }
    [{ access := Access.writable, type := Bool }, { access := Access.writable, type := Bool },
      { access := Access.writable, type := ℕ }]
in the application
  Member.there shared✝
-/
#guard_msgs (positions := true) in
example : Component [] (List (Item Nat)) (List Unit) := named%
  state% shared := (0 : Nat);
  state% ignored := false;
  .list .self "Rows"
    { inputs := inputs[.ui ref[shared]], run := toString }
    "Add" (Item.mkWithoutUuid 0) (.computed "Row" "value")
