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
      const snapshot = model.send({ event: { message: event } });
      if (snapshot.render) render(snapshot);
      for (const { url, ...request } of snapshot.effects) {
        try {
          const response = await fetch(url, request);
          await dispatch({ complete: { status: response.status, body: await response.text() } });
        } catch (error) { await dispatch({ failed: { message: message(error) } }); }
      }
    } catch (error) { fail(error); }
  }
  function render(snapshot: FormSnapshot) {
    let focus: HTMLElement | undefined;
    function node(tree: DisplayView | null): HTMLElement | DocumentFragment {
      if (!tree) return document.createDocumentFragment();
      const view = tree.element;
      const element = document.createElement(view.tag);
      for (const [name, value] of view.attributes) element.setAttribute(name, value);
      if (view.text !== null) element.textContent = view.text;
      for (const child of view.children) element.append(node(child));
      if (view.value !== null && (element instanceof HTMLInputElement || element instanceof HTMLSelectElement)) element.value = view.value;
      if (view.checked !== null && element instanceof HTMLInputElement) element.checked = view.checked;
      for (const binding of view.bindings) element.addEventListener(binding.event, event => {
        event.preventDefault();
        const input = document.getElementById(binding.source) as HTMLInputElement | HTMLSelectElement | null;
        const argument = binding.argument === 'none' ? null : binding.argument === 'checked'
          ? (input as HTMLInputElement).checked : binding.argument === 'index' ? Number(input!.value) : input!.value;
        if (binding.command === 'draft') void dispatch({ draft: { key: binding.key, argument: input!.value } });
        else if (binding.command === 'apply') void dispatch({ apply: { key: binding.key, argument } });
        else void dispatch(binding.command);
      });
      if (view.focusKey !== null && view.focusKey === snapshot.focus) focus = element;
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
