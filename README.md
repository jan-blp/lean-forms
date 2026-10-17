# lean-forms

Typed forms in Lean with a Rust terminal UI.

Requires Linux or macOS, [elan](https://lean-lang.org/install/), Rust/Cargo 1.88+, and `cc`.

```sh
lake exe cache get
lake -q exe forms
```

The terminal uses Catppuccin Frappé by default. Select Catppuccin Latte with:

```sh
lake -q exe forms --theme latte
```

Available themes: `frappe` (default), `macchiato`, `mocha`, `latte`,
`ayu-light`, `ayu-dark`, and `nord`. All work with `thermostat` and `invoice`.

Use ↑/↓ to select, Enter to edit/save a draft field, Space to toggle, Esc to
cancel an edit, `q` to submit, and `x` (or Esc outside an editor) to cancel the form.
Choice fields use ↑/↓ then Enter.
Interruption cancels without returning a submitted value.

The registration demo requires an age between 18 and 120. Try `17`: it becomes
the draft value and an error appears. Submission is blocked until you correct it.

For a constraint involving two fields, run:

```sh
lake -q exe forms thermostat
```

The heating thermostat has Home and Away temperatures, both using the same refined
whole-degree temperature type (5–30 °C). Away temperature must not exceed Home temperature.
Change Home temperature from 22 to 16: the draft is allowed, but Away temperature 18 now exceeds it.
Change Away temperature to 16, then submit. Try 4 or 31 in either field to see the shared
range constraint. This demonstrates reusable local refinements and a parent constraint
relating the two fields.

For repeatable groups, run:

```sh
lake -q exe forms invoice
```

Select **Add item** or **Remove** and press Enter. Each invoice item has a
description, quantity, and unit price in cents; quantity and price must be positive.
An empty invoice is allowed. Each item has its own form scope, so visibility and
cross-field constraints inside an item refer to that item's fields.

`DataType.list element` denotes `List (DataType.denote element)`. Refining its items with
`RefinedDataType.list item` gives `List (RefinedDataType.ValidatedValue item)`, preserving every item's proofs.
Typed `Path` values can address a whole list; dynamic item indices are UI references
rebuilt after edits. List validation messages currently identify the collection,
rather than the particular failing item. Item forms cannot reference outer fields.

For a choice between geometric shapes with different payload types:

```sh
lake -q exe forms shapes
```

Choose **Dot** (no details), **Circle** (radius), or **Rectangle** (width and
height). Sizes must be at least 1. Try a radius of 0, then switch to Dot: a dot
needs no dimensions. Switch back to Circle to recover your unfinished draft.

The selector shows a ▾ marker, with the selected payload grouped beneath it.
Empty constructors show “No details required”; a ! marker flags a sum with a
validation error. Only the active constructor is validated. Esc cancels a selector edit.

`DataType.record fieldNames fieldTypes` indexes its fieldNames by an `Enum`, which bundles a
finite enumeration and unique string names. Its values are dependent functions:
`(field : fields.type) → DataType.denote (children field)`. Paths use field identities,
for example `.child .width .self`. Groups display fields in enumeration order.

Record JSON uses objects such as `{"width": "4", "height": "2"}`. Schemas carry ordered
arrays of `{ "name": ..., "type": ... }` entries; forms and expression branches are
keyed by those names. Serialized paths contain field names. Changing enumeration
order changes presentation order while preserving field and constructor identity.
Missing or extra record fields and unknown constructor names are rejected.

`DataType.sum tags constructors` denotes `SumValue (fun i => DataType.denote (constructors i))`.
`SumValue` has named `tag` and `payload` fields; the tag determines the payload's type.
`RefinedDataType.sum branches` preserves the selected payload's validation proofs.
`Form.sum` supplies a label, a local form for each payload, and
initial draft values for each constructor. The `tags` enum gives constructors typed
identities and unique labels used for both display and serialization. An empty record represents a constructor without
payload fields, so optional values can be modeled as a two-constructor sum.

Sum JSON uses named tags, such as `{"tag": "circle", "value": "3"}`. Only the
active payload crosses the submission boundary; cached drafts live in the editor
for the current session. Sums compose with records, lists, and other sums.
Constructor forms and predicates use payload-local scopes and cannot reference outer
fields. `Expr.cases subject branches` evaluates the selected branch in its
payload's scope. Every constructor has a branch, and all branches share a result type
(which need not be boolean). Constructor constraints use `true` for inactive branches. Typed `Path` values address a whole
sum, not a conditional payload; dynamic UI references include the selected tag.
As with lists, validation messages currently point to the containing sum rather
than the individual payload field.

Refined types describe validated values independently of the UI:

```lean
def ageType : RefinedDataType .natural :=
  .refine (.base .natural)
    { condition := .and (.natLe (.value 18) (.project .self))
        (.natLe (.project .self) (.value 120))
      errorMessage := "Attendees must be between 18 and 120 years old."
      errorLocation := some ⟨.self⟩ }
```

`RefinedDataType.record` preserves each child's refined denotation. `RefinedDataType.refine` wraps
that denotation in a subtype whose proof satisfies the constraint. A parent constraint can
compare multiple fields using typed paths, as in `Forms/ExampleForms/Thermostat.lean`.
`Constraint.weaken` adapts reusable constraints to a larger scope, including diagnostic paths.

The editor holds `DataType.denote` drafts. `RefinedDataType.validate` constructs `RefinedDataType.ValidatedValue`
values with proofs; `RefinedDataType.erase` extracts their underlying data. Initial values
may be supplied as drafts, and their errors appear immediately. Hidden fields
still validate: visibility is presentation, not a validation condition.

The JSON protocol carries the same expressions to Rust for feedback. Lean checks
submitted JSON against the complete refined type again before constructing proofs.
The editor API returns `Option (RefinedDataType.ValidatedValue refined)`: `none` means cancellation.

Run checks:

```sh
lake test
CARGO_HOME="$PWD/.lake/cargo-home" cargo test --locked --manifest-path native/tui/Cargo.toml --target-dir .lake/tui
python3 tools/test_terminal.py
```

## Future reading

- [The Essence of Form Abstraction](https://homepages.inf.ed.ac.uk/slindley/papers/formlets-essence.pdf).
- [Yesod forms](https://www.yesodweb.com/book/forms).

## Example selection and completion

Run an example by name: `lake exe forms person`. Omitting the name selects
`person`. `lake exe forms --help` lists the examples and options available in
this version. Options can appear before or after the example name.

Enable completion for the current shell session, from the repository root:

```bash
source completions/forms.bash
```

```fish
source completions/forms.fish
```

Then type `lake exe forms ` and press Tab. Completion also works with
`lake -q exe forms`, `.lake/build/bin/forms`, or `forms` on your PATH.
The shell scripts query the executable; parsing, help, and completion share the
same registries. Through Lake, completion rebuilds the executable when needed.
The scripts do not change your shell startup files.

Run `python3 tools/test_cli.py` after building to check parsing and completion
against both Bash and Fish (both shells must be installed for this check).

Dates use `YYYY-MM-DD` (years 0001–9999). In the calendar, h/l moves a day,
k/j a week, and Page Up/Down a month. `i` or Enter focuses the input; Enter saves.
Esc returns to the calendar, then cancels.

`booking` demonstrates date ranges and date ordering.

`location` demonstrates dependent Country/City choices using sums.
