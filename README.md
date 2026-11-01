# lean-forms

Requires Linux or macOS, [elan](https://lean-lang.org/install/), Rust/Cargo 1.88+, and `cc`.

Run in an interactive terminal:

```sh
lake exe cache get
lake -q exe forms
lake -q exe forms counter
lake -q exe forms --help
```

↑/↓ selects; Enter edits/saves; Space toggles; Esc cancels an edit;
`q` submits; `x` cancels the form.

Web client (requires Node.js and npm; open `http://127.0.0.1:8080`):

```sh
npm --prefix web ci
lake -q exe forms-web --open
lake -q exe forms-web person --port 8081
```

Tab completion: `source completions/forms.bash` (Bash) or
`source completions/forms.fish` (Fish).
