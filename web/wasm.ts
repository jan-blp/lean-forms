import type { CompiledDescriptor, FormSnapshot } from './protocol.js';

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
    validate() { update('validate'); },
    serverError(status: number, body: string) { update('serverError', { status, body }); },
    summary() { check(); return snapshot.summary; },
    submissionBlocked() { check(); return snapshot.submissionBlocked; },
    reset() { update('reset'); },
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
