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

To run the Lean evaluator directly in the browser:

```sh
make -f experiments/wasm/Makefile setup
make -f experiments/wasm/Makefile
lake -q exe forms-web
# Open http://127.0.0.1:8080/?evaluator=wasm
```

The build uses Lean's normal C output and Emscripten. It builds the full Lean
runtime and standard libraries with upstream CMake, compiles the application's
dependencies supplied by Lake, and links an ES module plus a WebAssembly binary.
Generated C and module initialization are used unchanged. The first build is
large and slow; subsequent builds reuse the runtime and compiled objects.
Build prerequisites are CMake, Make, a C++ build environment, Python 3, curl,
Git, and patch. `setup` downloads pinned Lean 4.35.0 and Emscripten 7.0.0 into
`.lake/wasm/toolchains` and applies a compatibility patch correcting runtime FFI
signatures and the layout of static data on wasm32. The upstream build also
downloads libuv on its first run.

TypeScript calls the compiled Lean code through [web/wasm.ts](web/wasm.ts):

```ts
import { loadWasmEvaluator } from './wasm.js';

const evaluate = await loadWasmEvaluator();
const result = evaluate(
  { kind: 'project', path: [] },
  '42',
  { kind: 'natural' },
);
// result.value === '42'
```

The same generated module runs in Node.js. Run `npm --prefix web run test:wasm`
to compare its results with native Lean and test the TypeScript integration.
With Firefox installed, run `FORMS_WASM_TEST=1 node tools/test_browser.mjs`
after `lake build forms-web` to test the browser UI with the compiled evaluator.
The browser host must send `Cross-Origin-Opener-Policy: same-origin` and
`Cross-Origin-Embedder-Policy: require-corp`, because the upstream runtime uses
shared memory. The included web server sets these headers. Other hosts must
also serve `.wasm` as `application/wasm` and use HTTPS (or localhost).

Tab completion: `source completions/forms.bash` (Bash) or
`source completions/forms.fish` (Fish).
