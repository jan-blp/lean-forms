# lean-forms

Typed forms in Lean with a Rust terminal UI. Supports named records, sums, lists,
conditional visibility, and refinements. Lean validates submissions and constructs proofs.

Requires Linux or macOS, [elan](https://lean-lang.org/install/), Rust/Cargo 1.88+, and `cc`.

```sh
lake exe cache get
lake -q exe forms
```

Examples: `person` (default), `thermostat`, `invoice`, and `shapes`.
See [their source](Forms/ExampleForms) for the authoring API.

```sh
lake -q exe forms shapes --theme latte
lake -q exe forms --help
```

↑/↓ selects; Enter edits/saves; Space toggles; Esc cancels an edit;
`q` submits; `x` cancels the form. Invalid drafts block submission.

Groups default to enum order. Override with
`displayOrder := Equiv.swap .width .height` on `Form.group`.

Shell completion: source `completions/forms.bash` or `completions/forms.fish`.

Checks:

```sh
lake build
lake test
CARGO_HOME="$PWD/.lake/cargo-home" cargo test --locked --manifest-path native/tui/Cargo.toml --target-dir .lake/tui
python3 tools/test_terminal.py
python3 tools/test_cli.py  # requires Bash and Fish
```
