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

`DataType.list element` denotes `List element.denote`. Refining its items with
`RefinedDataType.list item` gives `List item.ValidatedValue`, preserving every item's proofs.
Typed `Path` values can address a whole list; dynamic item indices are UI references
rebuilt after edits. List validation messages currently identify the collection,
rather than the particular failing item. Item forms cannot reference outer fields.

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
The editor API returns `Option refined.ValidatedValue`: `none` means cancellation.

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

Records use an `Enum` of typed field identities with unique string names.
`DataType.record fieldNames fieldTypes` denotes `(field : fieldNames.type) → DataType.denote (fieldTypes field)`.
Groups follow enumeration order; their display labels are independent of record field names.
Record values serialize as JSON objects and paths use field names.

Dates use `YYYY-MM-DD` (years 0001–9999). In the calendar, h/l moves a day,
k/j a week, and Page Up/Down a month. `i` or Enter focuses the input; Enter saves.
Esc returns to the calendar, then cancels.

`booking` demonstrates date ranges and date ordering.
