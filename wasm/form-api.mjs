import createModule from '../.lake/wasm/forms.mjs';

// Raw transport and allocation instrumentation for integration tests.
export async function createFormRuntime() {
  const module = await createModule();
  module._forms_init();
  const encoder = new TextEncoder();
  return {
    form(text) {
      if (typeof text !== 'string') throw new TypeError('Expected JSON text');
      return JSON.parse(module.ccall('forms_request', 'string',
        ['string', 'number'], [text, encoder.encode(text).length]));
    },
    allocatedBytes: () => module._forms_allocated_bytes(),
  };
}
