# lean-forms

Requires Linux or macOS, [elan](https://lean-lang.org/install/), Node.js 22+,
npm, CMake, Make, a C++ compiler, Python 3, curl, Git, and patch.

```sh
lake exe cache get
npm ci
make -f wasm/makefile setup
make -f wasm/makefile
lake -q exe forms-web person --open
```

Rebuild Wasm after changing a form. The first build downloads toolchains and takes time.
Mathlib and Batteries use pinned fork releases with meta-only tactic imports to keep tactics out of the Wasm runtime. Native and Wasm builds share these dependencies.
The app opens at
`http://127.0.0.1:8080`; run `lake -q exe forms-web --help` for options.
Apply or Enter saves a field edit; Submit applies pending edits, then sends the values.
