# lean-forms

Typed forms in Lean with a Rust terminal UI.

Requires Linux or macOS, [elan](https://lean-lang.org/install/), Rust/Cargo 1.88+, and `cc`.

```sh
lake exe cache get
lake -q exe forms
```

Use ↑/↓ to select, Enter to edit/save, Space to toggle, Esc to cancel editing, and `q` to quit.
Choice fields use ↑/↓ then Enter to save.

Run checks:

```sh
lake test
CARGO_HOME="$PWD/.lake/cargo-home" cargo test --locked --manifest-path native/tui/Cargo.toml --target-dir .lake/tui
python3 tools/test_terminal.py
```

## Future reading

- [The Essence of Form Abstraction](https://homepages.inf.ed.ac.uk/slindley/papers/formlets-essence.pdf).
- [Yesod forms](https://www.yesodweb.com/book/forms).

Select a palette with `lake exe forms --theme latte`. Available themes: `frappe`
(default), `macchiato`, `mocha`, `latte`, `ayu-light`, `ayu-dark`, and `nord`.

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
`DataType.record fields children` denotes `(field : fields.type) → DataType.denote (children field)`.
Groups follow enumeration order; their display labels are independent of schema names.
Record values serialize as JSON objects and paths use field names.

Dates use `YYYY-MM-DD` (years 0001–9999). In the calendar, h/l moves a day,
k/j a week, and Page Up/Down a month. `i` or Enter focuses the input; Enter saves.
Esc returns to the calendar, then cancels.
