import type * as Wire from './protocol.js';

interface WasmModule {
  _forms_init(): void;
  ccall(name: string, result: string, types: string[], args: (string | number)[]): string;
}
interface Runtime { form(request: Wire.Request): Wire.Response }
let loading: Promise<Runtime> | undefined;

export async function openCompiledForm(descriptor: Wire.CompiledDescriptor) {
  const runtime = await (loading ??= load());
  const opened = runtime.form({ open: { descriptor } });
  if (typeof opened !== 'object' || !('opened' in opened)) throw new Error('Expected an opened form.');
  let snapshot = opened.opened.snapshot;
  let disposed = false;
  function check() { if (disposed) throw new Error('Form model is disposed.'); }
  return {
    snapshot() { check(); return structuredClone(snapshot); },
    send(request: Wire.Command) {
      check();
      const response = runtime.form({ send: { handle: opened.opened.handle, request } });
      if (typeof response !== 'object' || !('updated' in response)) throw new Error('Expected an updated form.');
      snapshot = response.updated.snapshot;
      return structuredClone(snapshot);
    },
    dispose() {
      if (!disposed) { runtime.form({ dispose: { handle: opened.opened.handle } }); disposed = true; }
    },
  };
}

async function load(): Promise<Runtime> {
  // A variable URL keeps the generated Emscripten module outside TypeScript's
  // source graph. It is packaged by wasm/makefile.
  const url = new URL('./wasm/forms.mjs', import.meta.url).href;
  const { default: createModule } = await import(url);
  const module: WasmModule = await createModule();
  module._forms_init();
  const encoder = new TextEncoder();
  function form(input: Wire.Request): Wire.Response {
    const request = JSON.stringify(input);
    if (request === undefined) throw new Error('Expected a JSON request.');
    let text: string;
    try {
      text = module.ccall('forms_request', 'string',
        ['string', 'number'], [request, encoder.encode(request).length]);
    } catch (error) {
      // An aborted instance (e.g. stack overflow) is unusable; reload on next use.
      loading = undefined;
      throw error;
    }
    const response = JSON.parse(text) as Wire.Success | Wire.Failure;
    if ('error' in response) throw new Error(response.error);
    return response.value;
  }
  return { form };
}
