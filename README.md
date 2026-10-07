# lean-forms

With [elan](https://lean-lang.org/install/) installed, run from the repository:

```sh
lake exe cache get
lake exe forms
```

Select a field number, then enter its new value. Enter `q` to quit.

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
