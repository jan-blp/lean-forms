import type { Evaluator, Schema, Value } from './protocol.js';

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
  return (expression, value, schema) => {
    if (!schema) throw new Error('Missing input schema for WebAssembly evaluation.');
    const args: (string | number)[] = [];
    for (const item of [schema, expression, value]) {
      const text = JSON.stringify(item);
      args.push(text, encoder.encode(text).length);
    }
    const response = JSON.parse(module.ccall('json_run_typed', 'string',
      ['string', 'number', 'string', 'number', 'string', 'number'], args)) as
      { ok: true; value: Value; schema: Schema } | { ok: false; error: string };
    if (!response.ok) throw new Error(response.error);
    return { value: response.value, schema: response.schema };
  };
}
