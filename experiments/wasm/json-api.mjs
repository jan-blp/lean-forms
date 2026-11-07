import createModule from '../../.lake/wasm/json.mjs';

// Initialize once, then evaluate JSON text with structured success/error results.
// This prototype decodes on every call; it does not retain expression handles.
export async function createEvaluator(options) {
  const module = await createModule(options);
  module._json_init();
  const encoder = new TextEncoder();
  function request(entry, ...items) {
    const args = [];
    for (const text of items) {
      if (typeof text !== 'string') throw new TypeError('Expected JSON text');
      args.push(text, encoder.encode(text).length);
    }
    return JSON.parse(module.ccall(entry, 'string',
      items.flatMap(() => ['string', 'number']), args));
  }
  return {
    // Compares against native results, which carry no result schema.
    evaluate: (...args) => {
      const { schema, ...result } = request('json_run_typed', ...args);
      return result;
    },
    check: (...args) => request('json_run_checker', ...args),
    form: requestJson => request('json_run_form', requestJson),
    normalize: (...args) => request('json_run_normalize', ...args),
    validate: (...args) => request('json_run_validation', ...args),
    // Experiment instrumentation, not part of the evaluation protocol.
    allocatedBytes: () => module._wasm_allocated_bytes(),
  };
}
