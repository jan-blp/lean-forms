# lean-forms

Typed forms in Lean with a Rust terminal UI. Supports named records, sums, lists, dates,
conditional visibility, disabling, computed values, and refinements. Lean validates submissions and constructs proofs.

Requires Linux or macOS, [elan](https://lean-lang.org/install/), Rust/Cargo 1.88+, and `cc`.

```sh
lake exe cache get
lake -q exe forms
```

Examples:

- [`person`](Forms/ExampleForms/Person.lean) (default): nested records, enum choices, conditional disabling, age validation.
- [`thermostat`](Forms/ExampleForms/Thermostat.lean): shared field refinements and validation across fields.
- [`invoice`](Forms/ExampleForms/Invoice.lean): editable lists, item validation, computed subtotals and total.
- [`shapes`](Forms/ExampleForms/Shapes.lean): sums with empty, scalar, and record payloads; validation per constructor.
- [`booking`](Forms/ExampleForms/Booking.lean): calendar dates, leap-year validation, inclusive date ranges, and date ordering.
- [`location`](Forms/ExampleForms/Location.lean): dependent Country/City choices using sums and separate city enums.

```sh
lake -q exe forms shapes --theme latte
lake -q exe forms --help
```

↑/↓ selects; Enter edits/saves; Space toggles; Esc cancels an edit;
`q` submits; `x` cancels the form. Invalid drafts block submission.

Groups default to enum order. Override with
`displayOrder := Equiv.swap .width .height` on `Form.group`.

`Form.computed label expression body` appends a read-only value; see the invoice total.

Dates use `YYYY-MM-DD`, with years 0001–9999. In the calendar,
h/l moves a day, k/j a week, and Page Up/Down a month (arrows also work).
`i` or Enter focuses the input; Enter saves. Esc returns to the calendar, then cancels.

Shell completion: source `completions/forms.bash` or `completions/forms.fish`.

Checks:

```sh
lake build
lake test
CARGO_HOME="$PWD/.lake/cargo-home" cargo test --locked --manifest-path native/tui/Cargo.toml --target-dir .lake/tui
python3 tools/test_terminal.py
python3 tools/test_cli.py  # requires Bash and Fish
```

## Presentations

Prepare successive sessions on the `presentations` branch. Tags named
`presentation-1`, `presentation-2`, and so on capture each session's slides and
matching demo code. A tag may mark a draft while a session is being prepared;
keep the delivered tag fixed after presenting.

Present from a detached worktree at the selected tag. Create worktrees as sibling
directories of this repository. For example, from the repository root:

```sh
git worktree add --detach ../lean-forms-presentation-1 refs/tags/presentation-1
make -C ../lean-forms-presentation-1/presentation build
```

The PDF is `presentation/slides.pdf` inside that worktree. Continue preparing the
next session on `presentations`; changes there do not alter tagged snapshots.
