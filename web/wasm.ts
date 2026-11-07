import type { Evaluator, Schema, Value } from './protocol.js';
import type { ResolvedError } from './validation.js';

interface WasmModule {
  _json_init(): void;
  ccall(name: string, result: string, types: string[], args: (string | number)[]): string;
}
let loading: Promise<Evaluator> | undefined;

export function loadWasmEvaluator(): Promise<Evaluator> {
  return loading ??= load();
}

async function load(): Promise<Evaluator> {
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
  return evaluator;
}
