# lean-forms

Requires Linux or macOS, [elan](https://lean-lang.org/install/), Node.js 22+, and npm.

Run the web client (opens `http://127.0.0.1:8080`):

```sh
lake exe cache get
npm --prefix web ci
lake -q exe forms-web --open
lake -q exe forms-web person --port 8081
lake -q exe forms-web --help
```

Apply or Enter saves a field edit; Submit sends the applied values.

Tab completion: `source completions/forms.bash` (Bash) or
`source completions/forms.fish` (Fish).
