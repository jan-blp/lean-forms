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

Web client (requires Node.js 22+ and npm; open `http://127.0.0.1:8080`):

```sh
npm --prefix web ci
lake -q exe forms-web --open
lake -q exe forms-web person --port 8081
```

Apply or Enter saves a field edit; Submit sends the applied values.

Tab completion: `source completions/forms.bash` (Bash) or
`source completions/forms.fish` (Fish).

A server-only refinement can use a pure, decidable Lean predicate outside the
expression language:

```lean
def evenNumber : Forms.RefinedDataType .natural :=
  .serverRefine (.base .natural)
    (.require (fun n => n % 2 = 0)
      (fun n => s!"{n} must be even.") (.fields [.self]))
```

The browser receives only the inner refinement. Submission validation enforces
the predicate on the server and returns its errors through the usual validation
response. The validated Lean value retains a proof of the predicate. Targets
are required: use `.global` for a form-wide error or `.fields [.self]` for the
value itself. This API is pure and does not perform IO or database lookups.
