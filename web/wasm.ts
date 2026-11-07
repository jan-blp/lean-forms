import type { CompiledDescriptor, Evaluator, FormSnapshot, Schema, Value } from './protocol.js';
import type { ResolvedError } from './validation.js';

interface WasmModule {
  _json_init(): void;
  ccall(name: string, result: string, types: string[], args: (string | number)[]): string;
}
interface Runtime { evaluator: Evaluator; form(request: unknown): unknown }
let loading: Promise<Runtime> | undefined;

export async function loadWasmEvaluator(): Promise<Evaluator> {
  return (await (loading ??= load())).evaluator;
}

export async function openCompiledForm(descriptor: CompiledDescriptor) {
  const runtime = await (loading ??= load());
  const opened = runtime.form({ operation: 'open', ...descriptor }) as { handle: string; snapshot: FormSnapshot };
  let snapshot = opened.snapshot;
  let disposed = false;
  function check() { if (disposed) throw new Error('Form model is disposed.'); }
  function update(operation: string, fields: object = {}) {
    check();
    snapshot = runtime.form({ operation, handle: opened.handle, ...fields }) as FormSnapshot;
  }
  return {
    title: snapshot.title,
    view() { check(); return structuredClone(snapshot.view); },
    controls() { check(); return structuredClone(snapshot.controls); },
    errors() { check(); return structuredClone(snapshot.errors); },
    submission() { check(); return structuredClone(snapshot.submission); },
    apply(key: string, argument?: unknown) {
      update('apply', { key, ...(argument === undefined ? {} : { argument }) });
    },
    reset() { update('reset'); },
    dispose() {
      if (!disposed) { runtime.form({ operation: 'dispose', handle: opened.handle }); disposed = true; }
    },
  };
}

async function load(): Promise<Runtime> {
  // A variable URL keeps the generated Emscripten module outside TypeScript's
  // source graph. It is packaged by experiments/wasm/Makefile.
  const url = new URL('./wasm/json.mjs', import.meta.url).href;
  const { default: createModule } = await import(url);
  const module: WasmModule = await createModule();
  module._json_init();
  const encoder = new TextEncoder();
  function request(name: string, ...items: unknown[]): unknown {
    const args: (string | number)[] = [];
    for (const item of items) {
      const text = JSON.stringify(item);
      if (text === undefined) throw new Error('Expected a JSON value.');
      args.push(text, encoder.encode(text).length);
    }
    let text: string;
    try {
      text = module.ccall(name, 'string',
        items.flatMap(() => ['string', 'number']), args);
    } catch (error) {
      // An aborted instance (e.g. stack overflow) is unusable; reload on next use.
      loading = undefined;
      throw error;
    }
    const response = JSON.parse(text);
    if (!response.ok) throw new Error(response.error);
    return response;
  }
  const evaluator: Evaluator = (expression, value, schema) => {
    if (!schema) throw new Error('Missing input schema for WebAssembly evaluation.');
    const result = request('json_run_typed', schema, expression, value) as { value: Value; schema: Schema };
    return { value: result.value, schema: result.schema };
  };
  evaluator.runChecker = (checker, schema, value) =>
    (request('json_run_checker', schema, checker, value) as { value: ResolvedError[] }).value;
  evaluator.validate = (refinement, schema, value) =>
    (request('json_run_validation', schema, refinement, value) as { value: ResolvedError[] }).value;
  evaluator.normalize = (schema, value) =>
    (request('json_run_normalize', schema, value) as { value: Value }).value;
  return { evaluator, form: input => (request('json_run_form', input) as { value: unknown }).value };
}
