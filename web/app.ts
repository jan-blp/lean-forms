import { openCompiledForm } from './wasm.js';
import type { DisplayControl as Control, CompiledDescriptor, Value, DisplayView as View } from './protocol.js';

function required<T extends HTMLElement>(selector: string, type: { new(): T }): T {
  const node = document.querySelector(selector);
  if (!(node instanceof type)) throw new Error(`Missing or invalid element: ${selector}`);
  return node;
}

function unsupported(value: never): never {
  throw new Error(`Unsupported variant: ${JSON.stringify(value)}`);
}

function message(error: unknown): string {
  return error instanceof Error ? error.message : String(error);
}

const container = required('#controls', HTMLElement);
const submit = required('#submit', HTMLButtonElement);
const reset = required('#reset', HTMLButtonElement);
const count = required('#count', HTMLElement);
const status = required('#status', HTMLElement);
const result = required('#result', HTMLDetailsElement);

function announce(message: string, error = false) {
  status.textContent = message;
  status.classList.toggle('error', error);
}

function element<K extends keyof HTMLElementTagNameMap>(tag: K, text?: string, className?: string): HTMLElementTagNameMap[K] {
  const node = document.createElement(tag);
  if (text !== undefined) node.textContent = text;
  if (className) node.className = className;
  return node;
}

function mount(model: Awaited<ReturnType<typeof openCompiledForm>>) {
  let pending = false;
  const drafts = new Map<string, string>();

  function act(...[control, argument]:
    | [control: Extract<Control, { kind: 'button' }>]
    | [control: Extract<Control, { kind: 'choice' }>, argument: string]
    | [control: Extract<Control, { kind: 'editor' }>, argument: Value]
  ) {
    if (pending) return;
    try {
      if (drafts.size > 0 && (control.kind === 'choice' ||
        (control.kind === 'button' && !control.keepDrafts))) {
        announce('Apply your edits before using this control.', true);
        render(drafts.keys().next().value);
        return;
      }
      model.apply(control.key, argument);
      drafts.delete(control.key);
      result.hidden = true;
      announce('');
      render(control.key);
    } catch (error) {
      announce(message(error), true);
    }
  }

  function render(focusKey?: string) {
    container.replaceChildren();
    let focus: HTMLElement | undefined;
    const editable = new Set<string>();
    let errorId = 0;
    function renderNode(node: View | null): HTMLElement | DocumentFragment {
      const rendered = renderContent(node);
      if (node && node.messages !== undefined && rendered instanceof HTMLElement) {
        const feedback = element('p', node.messages, 'validation-error');
        feedback.id = `validation-error-${errorId++}`;
        rendered.append(feedback);
        const inputs = node.kind === 'editor' || node.kind === 'choice' ? rendered.querySelectorAll('input, select') : [];
        for (const input of inputs) {
          input.setAttribute('aria-invalid', 'true');
          const describedBy = input.getAttribute('aria-describedby');
          input.setAttribute('aria-describedby', [describedBy, feedback.id].filter(Boolean).join(' '));
        }
      }
      return rendered;
    }
    function renderContent(node: View | null): HTMLElement | DocumentFragment {
      if (!node) return document.createDocumentFragment();
      if (node.kind === 'element') {
        const rendered = element(node.tag, node.text);
        for (const [name, value] of node.attributes) rendered.setAttribute(name, value);
        for (const child of node.children) rendered.append(renderNode(child));
        return rendered;
      }
      if (node.kind === 'choice') {
        const label = element('label', node.label, 'choice');
        const select = element('select');
        for (const name of node.options) {
          const option = element('option', name);
          option.value = name;
          select.append(option);
        }
        select.value = node.value;
        select.disabled = pending || node.disabled;
        select.addEventListener('change', () => act(node, select.value));
        label.append(select);
        if (focusKey === node.key) focus = select;
        return label;
      }
      if (node.kind === 'button') {
        const button = element('button', node.label, 'action');
        button.type = 'button';
        button.disabled = pending || node.disabled;
        button.addEventListener('click', () => act(node));
        if (focusKey === node.key) focus = button;
        return button;
      }
      if (node.kind !== 'editor') return unsupported(node);
      const form = element('form', undefined, 'editor');
      const label = element('label', node.label);
      const input = element(node.input.tag);
      for (const [name, value] of node.input.attributes) input.setAttribute(name, value);
      for (const [value, label] of node.input.options) {
        const option = element('option', label);
        option.value = value;
        input.append(option);
      }
      input.value = node.input.value;
      if (input instanceof HTMLInputElement) input.checked = node.input.checked;
      input.disabled = pending || node.disabled;
      label.append(input);
      form.append(label);
      const argument = () => input instanceof HTMLInputElement && node.input.argument === 'checked' ? input.checked
        : node.input.argument === 'index' ? Number(input.value) : input.value;
      if (node.input.immediate) {
        input.addEventListener('change', () => act(node, argument()));
      } else {
        if (!input.disabled) {
          editable.add(node.key);
          const initial = input.value;
          input.value = drafts.get(node.key) ?? initial;
          input.addEventListener('input', () => {
            if (input.value === initial) drafts.delete(node.key);
            else drafts.set(node.key, input.value);
          });
        }
        const button = element('button', 'Apply');
        button.disabled = input.disabled;
        form.append(button);
      }
      form.addEventListener('submit', event => { event.preventDefault(); act(node, argument()); });
      if (focusKey === node.key) focus = input;
      return form;
    }
    container.append(renderNode(model.view()));
    for (const key of drafts.keys()) if (!editable.has(key)) drafts.delete(key);
    focus?.focus();
    const total = model.submission().actions.length;
    count.textContent = `${total} ${total === 1 ? 'action' : 'actions'}`;
    submit.disabled = pending;
    reset.disabled = pending;
    container.setAttribute('aria-busy', String(pending));
  }

  submit.addEventListener('click', async () => {
    if (pending) return;
    if (drafts.size > 0) {
      announce('Apply your edits before submitting.', true);
      render(drafts.keys().next().value);
      return;
    }
    model.validate();
    if (model.submissionBlocked()) {
      announce(model.summary(), true);
      render();
      return;
    }
    pending = true;
    const submission = model.submission();
    render();
    announce('Submitting…');
    try {
      const response = await fetch('/api/submit', {
        method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(submission),
      });
      if (!response.ok) {
        model.serverError(response.status, await response.text());
        throw new Error(model.summary());
      }
      announce('Submitted successfully.');
      required('#result pre', HTMLPreElement).textContent = JSON.stringify(submission.value, null, 2);
      result.hidden = false;
    } catch (error) {
      announce(message(error), true);
    } finally {
      pending = false;
      render();
    }
  });

  reset.addEventListener('click', () => {
    if (pending) return;
    drafts.clear();
    model.reset();
    result.hidden = true;
    announce('Started over.');
    render();
  });

  render();
}

try {
  const response = await fetch('/api/compiled-form');
  if (!response.ok) throw new Error('Could not load the form.');
  const descriptor = await response.json() as CompiledDescriptor;
  const model = await openCompiledForm(descriptor);
  required('#title', HTMLElement).textContent = model.title;
  document.title = `Lean Forms · ${model.title}`;
  mount(model);
  window.addEventListener('pagehide', event => { if (!event.persisted) model.dispose(); });
  container.dataset.runtime = 'compiled';
} catch (error) {
  container.setAttribute('aria-busy', 'false');
  count.textContent = '';
  announce(message(error), true);
}
