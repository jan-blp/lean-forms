import type { CompiledDescriptor, FormSnapshot, FormRequest } from './protocol.js';

interface WasmModule {
  _forms_init(): void;
  ccall(name: string, result: string, types: string[], args: (string | number)[]): string;
}
interface Runtime { form(request: unknown): unknown }
let loading: Promise<Runtime> | undefined;

export async function openCompiledForm(descriptor: CompiledDescriptor) {
  const runtime = await (loading ??= load());
  const opened = runtime.form({ operation: 'open', ...descriptor }) as { handle: string; snapshot: FormSnapshot };
  let snapshot = opened.snapshot;
  let disposed = false;
  function check() { if (disposed) throw new Error('Form model is disposed.'); }
  return {
    snapshot() { check(); return structuredClone(snapshot); },
    send(request: FormRequest) {
      check();
      snapshot = runtime.form({ ...request, handle: opened.handle }) as FormSnapshot;
      return structuredClone(snapshot);
    },
    dispose() {
      if (!disposed) { runtime.form({ operation: 'dispose', handle: opened.handle }); disposed = true; }
    },
  };
}

async function load(): Promise<Runtime> {
  // A variable URL keeps the generated Emscripten module outside TypeScript's
  // source graph. It is packaged by experiments/wasm/Makefile.
  const url = new URL('./wasm/forms.mjs', import.meta.url).href;
  const { default: createModule } = await import(url);
  const module: WasmModule = await createModule();
  module._forms_init();
  const encoder = new TextEncoder();
  function form(input: unknown): unknown {
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
    const response = JSON.parse(text);
    if (!response.ok) throw new Error(response.error);
    return response.value;
  }
  return { form };
}
