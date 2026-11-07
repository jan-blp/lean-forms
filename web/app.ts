import { openCompiledForm } from './wasm.js';
import type { CompiledDescriptor, DisplayView, FormSnapshot, FormEvent } from './protocol.js';

const root = document.querySelector('main')!;
const message = (error: unknown) => error instanceof Error ? error.message : String(error);
function fail(error: unknown) {
  root.replaceChildren(Object.assign(document.createElement('p'), { textContent: message(error), className: 'error', role: 'alert' }));
}

function mount(model: Awaited<ReturnType<typeof openCompiledForm>>) {
  async function dispatch(event: FormEvent) {
    try {
      const snapshot = model.send({ operation: 'event', ...event });
      if (snapshot.render) render(snapshot);
      for (const { url, ...request } of snapshot.effects) {
        try {
          const response = await fetch(url, request);
          await dispatch({ event: 'complete', status: response.status, body: await response.text() });
        } catch (error) { await dispatch({ event: 'failed', message: message(error) }); }
      }
    } catch (error) { fail(error); }
  }
  function render(snapshot: FormSnapshot) {
    let focus: HTMLElement | undefined;
    function node(view: DisplayView | null): HTMLElement | DocumentFragment {
      if (!view) return document.createDocumentFragment();
      const element = document.createElement(view.tag);
      for (const [name, value] of view.attributes) element.setAttribute(name, value);
      if (view.text !== undefined) element.textContent = view.text;
      for (const child of view.children) element.append(node(child));
      if (view.value !== undefined && (element instanceof HTMLInputElement || element instanceof HTMLSelectElement)) element.value = view.value;
      if (view.checked !== undefined && element instanceof HTMLInputElement) element.checked = view.checked;
      for (const binding of view.bindings) element.addEventListener(binding.event, event => {
        event.preventDefault();
        const input = document.getElementById(binding.source) as HTMLInputElement | HTMLSelectElement | null;
        const argument = binding.argument === 'none' ? undefined : binding.argument === 'checked'
          ? (input as HTMLInputElement).checked : binding.argument === 'index' ? Number(input!.value) : input!.value;
        void dispatch({ event: binding.command, key: binding.key, ...(argument === undefined ? {} : { argument }) });
      });
      if (view.focusKey === snapshot.focus) focus = element;
      return element;
    }
    root.replaceChildren(node(snapshot.view));
    document.title = `Lean Forms · ${snapshot.title}`;
    focus?.focus();
  }
  render(model.snapshot());
}

try {
  const response = await fetch('/api/compiled-form');
  if (!response.ok) throw new Error('Could not load the form.');
  const model = await openCompiledForm(await response.json() as CompiledDescriptor);
  mount(model);
  window.addEventListener('pagehide', event => { if (!event.persisted) model.dispose(); });
} catch (error) { fail(error); }
