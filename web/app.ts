import { createModel, formatValue, textValue } from './interpreter.js';
import type { Control, Specification, View } from './protocol.js';

function required<T extends HTMLElement>(selector: string): T {
  const node = document.querySelector<T>(selector);
  if (!node) throw new Error(`Missing element: ${selector}`);
  return node;
}

function message(error: unknown): string {
  return error instanceof Error ? error.message : String(error);
}

const container = required<HTMLElement>('#controls');
const submit = required<HTMLButtonElement>('#submit');
const reset = required<HTMLButtonElement>('#reset');
const count = required<HTMLElement>('#count');
const status = required<HTMLElement>('#status');
const result = required<HTMLDetailsElement>('#result');
let model: ReturnType<typeof createModel>;
let pending = false;
const drafts = new Map<string, string>();

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

function act(control: Control, argument?: unknown) {
  try {
    if (drafts.size > 0 && (control.kind === 'choice' ||
      (control.kind === 'button' && control.effect.kind !== 'appendDefault'))) {
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
  function renderNode(node: View | null): HTMLElement | DocumentFragment {
    if (!node) return document.createDocumentFragment();
    if (node.kind === 'stack' || node.kind === 'actionWidget') {
      const group = element('fieldset', undefined, 'component');
      if (node.label) group.append(element('legend', node.label));
      if (node.kind === 'actionWidget') {
        const display = formatValue(node.schema, node.value);
        group.append(element('output', display, 'value'));
      }
      for (const child of node.children) group.append(renderNode(child));
      return group;
    }
    if (node.kind === 'list') {
      const group = element('fieldset', undefined, 'component');
      group.append(element('legend', node.label));
      node.items.forEach((item, index) => {
        const row = element('fieldset', undefined, 'list-item');
        row.append(element('legend', `Item ${index + 1}`), renderNode(item.body), renderNode(item.remove));
        group.append(row);
      });
      group.append(renderNode(node.append));
      return group;
    }
    if (node.kind === 'sum') {
      const group = element('div', undefined, 'sum');
      group.append(renderNode(node.selector), renderNode(node.body));
      return group;
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
    if (node.kind === 'table') {
      const wrapper = element('div', undefined, 'table-scroll');
      const table = element('table');
      const head = element('thead');
      const headings = element('tr');
      for (const title of node.columns) {
        const cell = element('th', title);
        cell.scope = 'col';
        headings.append(cell);
      }
      head.append(headings);
      const body = element('tbody');
      for (const cells of node.rows) {
        const row = element('tr');
        for (const text of cells) row.append(element('td', text));
        body.append(row);
      }
      table.append(head, body);
      wrapper.append(table);
      return wrapper;
    }
    if (node.kind === 'text') return element('p', node.value, 'text');
    if (node.kind === 'computed') {
      const group = element('div', undefined, 'computed');
      const label = element('label', node.label);
      label.append(element('output', formatValue(node.schema, node.value)));
      group.append(label);
      return group;
    }
    if (node.kind === 'button') {
      const button = element('button', node.label, 'action');
      button.type = 'button';
      button.disabled = pending || node.disabled;
      button.addEventListener('click', () => act(node));
      if (focusKey === node.key) focus = button;
      return button;
    }
    const form = element('form', undefined, 'editor');
    const label = element('label', node.label);
    let input: HTMLInputElement | HTMLSelectElement;
    switch (node.widget) {
      case 'select': {
        if (node.schema.kind !== 'enum') throw new Error('Select requires an enum schema.');
        const select = element('select');
        input = select;
        node.schema.options.forEach((name, index) => {
          const option = element('option', name);
          option.value = String(index);
          select.append(option);
        });
        input.value = String(node.value);
        break;
      }
      case 'checkbox':
        input = element('input');
        input.type = 'checkbox';
        input.checked = Boolean(node.value);
        break;
      case 'textInput':
      case 'naturalInput':
      case 'dateInput':
        input = element('input');
        input.type = node.widget === 'dateInput' ? 'date' : 'text';
        input.value = textValue(node.value);
        if (node.widget === 'naturalInput') {
          input.inputMode = 'numeric';
          input.pattern = '[0-9]+';
          input.required = true;
        }
        if (node.widget === 'dateInput') {
          input.min = '0001-01-01';
          input.max = '9999-12-31';
          input.required = true;
        }
        break;
      default: throw new Error(`Unsupported widget: ${node.widget}`);
    }
    input.disabled = pending || node.disabled;
    label.append(input);
    form.append(label);
    const argument = () => input instanceof HTMLInputElement && node.widget === 'checkbox' ? input.checked
      : node.widget === 'select' ? Number(input.value) : input.value;
    if (node.widget === 'checkbox' || node.widget === 'select') {
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
  if (drafts.size > 0) {
    announce('Apply your edits before submitting.', true);
    render(drafts.keys().next().value);
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
      const body = await response.json();
      throw new Error(body.error || 'Submission failed.');
    }
    announce('Submitted successfully.');
    required<HTMLPreElement>('#result pre').textContent = JSON.stringify(submission.value, null, 2);
    result.hidden = false;
  } catch (error) {
    announce(message(error), true);
  } finally {
    pending = false;
    render();
  }
});

reset.addEventListener('click', () => {
  drafts.clear();
  model.reset();
  result.hidden = true;
  announce('Started over.');
  render();
});

try {
  const response = await fetch('/api/form');
  if (!response.ok) throw new Error('Could not load the form.');
  const spec = await response.json() as Specification;
  const title = ('label' in spec.form && spec.form.label) || 'Form';
  required<HTMLElement>('#title').textContent = title;
  document.title = `Lean Forms · ${title}`;
  model = createModel(spec);
  render();
} catch (error) {
  container.setAttribute('aria-busy', 'false');
  count.textContent = '';
  announce(message(error), true);
}
