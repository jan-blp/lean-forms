import createModule from '../../.lake/wasm/json.mjs';

// Initialize once, then evaluate JSON text with structured success/error results.
// This prototype decodes on every call; it does not retain expression handles.
export async function createEvaluator(options) {
  const module = await createModule(options);
  module._json_init();
  const encoder = new TextEncoder();
  function request(entry, inputSchemaJson, programJson, valueJson) {
    const args = [];
    for (const text of [inputSchemaJson, programJson, valueJson]) {
      if (typeof text !== 'string') throw new TypeError('Expected JSON text');
      args.push(text, encoder.encode(text).length);
    }
    return JSON.parse(module.ccall(entry, 'string',
      ['string', 'number', 'string', 'number', 'string', 'number'], args));
  }
  return {
    // Compares against native results, which carry no result schema.
    evaluate: (...args) => {
      const { schema, ...result } = request('json_run_typed', ...args);
      return result;
    },
    check: (...args) => request('json_run_checker', ...args),
    // Experiment instrumentation, not part of the evaluation protocol.
    allocatedBytes: () => module._wasm_allocated_bytes(),
  };
}
