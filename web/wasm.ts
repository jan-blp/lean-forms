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
  function request(name: string, schema: Schema, program: unknown, value: Value): unknown {
    const args: (string | number)[] = [];
    for (const item of [schema, program, value]) {
      const text = JSON.stringify(item);
      args.push(text, encoder.encode(text).length);
    }
    const response = JSON.parse(module.ccall(name, 'string',
      ['string', 'number', 'string', 'number', 'string', 'number'], args));
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
  return evaluator;
}
