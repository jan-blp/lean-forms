import type * as Wire from './protocol/Forms/Runtime/Wire.js';

interface WasmModule {
  _forms_init(): void;
  ccall(name: string, result: string, types: string[], args: (string | number)[]): string;
}
interface Runtime { form(request: Wire.Request): Wire.Response }

/** An open form in the compiled Lean runtime. */
export interface FormModel {
  snapshot(): Wire.Snapshot;
  send(command: Wire.Command): Wire.Snapshot;
  dispose(): void;
}

const loading = new Map<string, Promise<Runtime>>();

/** Opens `descriptor` in the Emscripten module at `moduleUrl` (the app's `forms.mjs`). */
export async function openCompiledForm(descriptor: Wire.CompiledDescriptor, moduleUrl: string | URL): Promise<FormModel> {
  const url = String(moduleUrl);
  let runtime = loading.get(url);
  if (!runtime) loading.set(url, runtime = load(url));
  const { form } = await runtime;
  const opened = form({ open: { descriptor } });
  if (typeof opened !== 'object' || !('opened' in opened)) throw new Error('Expected an opened form.');
  const { handle } = opened.opened;
  let snapshot = opened.opened.snapshot;
  let disposed = false;
  function check() { if (disposed) throw new Error('Form model is disposed.'); }
  return {
    snapshot() { check(); return structuredClone(snapshot); },
    send(request) {
      check();
      const response = form({ send: { handle, request } });
      if (typeof response !== 'object' || !('updated' in response)) throw new Error('Expected an updated form.');
      snapshot = response.updated.snapshot;
      return structuredClone(snapshot);
    },
    dispose() {
      if (!disposed) { form({ dispose: { handle } }); disposed = true; }
    },
  };
}

async function load(url: string): Promise<Runtime> {
  // A variable URL keeps the generated Emscripten module out of the bundle.
  const { default: createModule } = await import(url);
  const module: WasmModule = await createModule();
  module._forms_init();
  const encoder = new TextEncoder();
  function form(input: Wire.Request): Wire.Response {
    const request = JSON.stringify(input);
    let text: string;
    try {
      text = module.ccall('forms_request', 'string',
        ['string', 'number'], [request, encoder.encode(request).length]);
    } catch (error) {
      // An aborted instance (e.g. stack overflow) is unusable; reload on next use.
      loading.delete(url);
      throw error;
    }
    const response = JSON.parse(text) as Wire.Success | Wire.Failure;
    if ('error' in response) throw new Error(response.error);
    return response.value;
  }
  return { form };
}
