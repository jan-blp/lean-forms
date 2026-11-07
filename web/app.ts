import { openCompiledForm } from './wasm.js';
import type { CompiledDescriptor, DisplayView as View } from './protocol.js';

function required<T extends HTMLElement>(selector: string, type: { new(): T }): T {
  const node = document.querySelector(selector);
  if (!(node instanceof type)) throw new Error(`Missing or invalid element: ${selector}`);
  return node;
}
const container = required('#controls', HTMLElement);
const status = required('#status', HTMLElement);
const submit = required('#submit', HTMLButtonElement);
const reset = required('#reset', HTMLButtonElement);
const result = required('#result', HTMLDetailsElement);
const count = required('#count', HTMLElement);
const message = (error: unknown) => error instanceof Error ? error.message : String(error);
function fail(error: unknown) {
  status.textContent = message(error);
  status.classList.add('error');
}

function mount(model: Awaited<ReturnType<typeof openCompiledForm>>) {
  async function dispatch(event: string, fields: object = {}) {
    try {
      model.event(event, fields);
      if (event === 'draft') return;
      render();
      if (!model.ui().send) return;
      try {
        const response = await fetch('/api/submit', {
          method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(model.submission()),
        });
        await dispatch('complete', { status: response.status, body: response.ok ? '' : await response.text() });
      } catch (error) { await dispatch('failed', { message: message(error) }); }
    } catch (error) { fail(error); }
  }
  function render() {
    const ui = model.ui();
    let focus: HTMLElement | undefined;
    function node(view: View | null): HTMLElement | DocumentFragment {
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
        void dispatch(binding.command, { key: binding.key, ...(argument === undefined ? {} : { argument }) });
      });
      if (view.focusKey === ui.focus) focus = element;
      return element;
    }
    container.replaceChildren(node(model.view()));
    status.textContent = ui.status;
    status.classList.toggle('error', ui.error);
    count.textContent = ui.count;
    submit.disabled = reset.disabled = ui.pending;
    container.setAttribute('aria-busy', String(ui.pending));
    result.hidden = ui.result === null;
    required('#result pre', HTMLPreElement).textContent = ui.result ?? '';
    focus?.focus();
  }
  submit.addEventListener('click', () => void dispatch('submit'));
  reset.addEventListener('click', () => void dispatch('reset'));
  render();
}

try {
  const response = await fetch('/api/compiled-form');
  if (!response.ok) throw new Error('Could not load the form.');
  const model = await openCompiledForm(await response.json() as CompiledDescriptor);
  required('#title', HTMLElement).textContent = model.title;
  document.title = `Lean Forms · ${model.title}`;
  mount(model);
  window.addEventListener('pagehide', event => { if (!event.persisted) model.dispose(); });
  container.dataset.runtime = 'compiled';
} catch (error) {
  container.setAttribute('aria-busy', 'false');
  count.textContent = '';
  fail(error);
}
