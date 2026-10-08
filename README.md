# lean-forms

Typed forms in Lean with a Rust terminal UI.

Requires Linux or macOS, [elan](https://lean-lang.org/install/), Rust/Cargo 1.88+, and `cc`.

```sh
lake exe cache get
lake -q exe forms
```

Use ↑/↓ to select, Enter to edit/save, Space to toggle, Esc to cancel editing, and `q` to quit.
Add `--plain` for the line interface.

Run checks:

```sh
lake test
CARGO_HOME="$PWD/.lake/cargo-home" cargo test --locked --manifest-path native/ratatui/Cargo.toml --target-dir .lake/ratatui
python3 tools/test_terminal.py
```

## Future reading

- [The Essence of Form Abstraction](https://homepages.inf.ed.ac.uk/slindley/papers/formlets-essence.pdf).
- [Yesod forms](https://www.yesodweb.com/book/forms).
