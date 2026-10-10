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
`ayu-light`, `ayu-dark`, and `nord`. All work with `--thermostat`.

Use ↑/↓ to select, Enter to edit/save a draft field, Space to toggle, Esc to
cancel an edit, `q` to submit, and `x` (or Esc outside an editor) to cancel the form.
Choice fields use ↑/↓ then Enter.
Interruption cancels without returning a submitted value.

The registration demo requires an age between 18 and 120. Try `17`: it becomes
the draft value and an error appears. Submission is blocked until you correct it.

For a constraint involving two fields, run:

```sh
lake -q exe forms --thermostat
```

The heating thermostat has Home and Away temperatures, both using the same refined
whole-degree temperature type (5–30 °C). Away temperature must not exceed Home temperature.
Change Home temperature from 22 to 16: the draft is allowed, but Away temperature 18 now exceeds it.
Change Away temperature to 16, then submit. Try 4 or 31 in either field to see the shared
range constraint. This demonstrates reusable local refinements and a parent constraint
relating the two fields.

Refined types describe validated values independently of the UI:

```lean
def ageType : RefinedDataType .natural :=
  .refine (.base .natural)
    { condition := .and (.natLe (.value 18) (.project .here))
        (.natLe (.project .here) (.value 120))
      errorMessage := "Attendees must be between 18 and 120 years old."
      errorLocation := some ⟨.here⟩ }
```

`RefinedDataType.group` preserves each child's refined denotation. `RefinedDataType.refine` wraps
that denotation in a subtype whose proof satisfies the constraint. A parent constraint can
compare multiple fields using typed paths, as in `Forms/ExampleForms/Thermostat.lean`.
`Constraint.weaken` adapts reusable constraints to a larger scope, including diagnostic paths.

The editor holds `DataType.denote` drafts. `RefinedDataType.validate` constructs `RefinedDataType.denote`
values with proofs; `RefinedDataType.erase` extracts their underlying data. Initial values
may be supplied as drafts, and their errors appear immediately. Hidden fields
still validate: visibility is presentation, not a validation condition.

The JSON protocol carries the same expressions to Rust for feedback. Lean checks
submitted JSON against the complete refined type again before constructing proofs.
The editor API returns `Option refined.denote`: `none` means cancellation.

Run checks:

```sh
lake test
CARGO_HOME="$PWD/.lake/cargo-home" cargo test --locked --manifest-path native/tui/Cargo.toml --target-dir .lake/tui
python3 tools/test_terminal.py
```

## Future reading

- [The Essence of Form Abstraction](https://homepages.inf.ed.ac.uk/slindley/papers/formlets-essence.pdf).
- [Yesod forms](https://www.yesodweb.com/book/forms).
