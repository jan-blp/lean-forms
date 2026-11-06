import { sameLocation } from './validation.js';
import { createModel, formatValue, textValue } from './interpreter.js';
import type { Control, Specification, SubmissionError, ValidationError, Value, View } from './protocol.js';

function required<T extends HTMLElement>(selector: string, type: { new(): T }): T {
  const node = document.querySelector(selector);
  if (!(node instanceof type)) throw new Error(`Missing or invalid element: ${selector}`);
  return node;
}

function unsupported(value: never): never {
  throw new Error(`Unsupported variant: ${JSON.stringify(value)}`);
}

function isLocation(value: unknown): boolean {
  return Array.isArray(value) && value.every(step => {
    if (typeof step !== 'object' || step === null) return false;
    switch (step.kind) {
      case 'field': return typeof step.name === 'string';
      case 'constructor': return typeof step.tag === 'string';
      case 'item': return typeof step.index === 'string' && /^[0-9]+$/.test(step.index);
      default: return false;
    }
  });
}

function isValidationError(value: unknown): value is ValidationError {
  if (typeof value !== 'object' || value === null || !('message' in value) ||
    typeof value.message !== 'string' || !('targets' in value)) return false;
  const targets = value.targets;
  if (typeof targets !== 'object' || targets === null || !('kind' in targets)) return false;
  if (targets.kind === 'global') return true;
  if (targets.kind === 'invalidTarget') return 'location' in targets && isLocation(targets.location);
  return targets.kind === 'locations' && 'locations' in targets && Array.isArray(targets.locations) &&
    targets.locations.length > 0 && targets.locations.every(isLocation);
}

async function submissionError(response: Response): Promise<SubmissionError> {
  const fallback: SubmissionError = { kind: 'request', message: `Submission failed (HTTP ${response.status}).` };
  try {
    const body: unknown = await response.json();
    if (typeof body !== 'object' || body === null || !('error' in body)) return fallback;
    const error = body.error;
    if (typeof error !== 'object' || error === null || !('kind' in error) ||
      !('message' in error) || typeof error.message !== 'string' || !error.message) return fallback;
    if (error.kind === 'request' || error.kind === 'replay') {
      return { kind: error.kind, message: error.message };
    }
    if (error.kind === 'validation' && 'errors' in error && Array.isArray(error.errors) &&
      error.errors.every(isValidationError)) {
      return { kind: 'validation', message: error.message, errors: error.errors };
    }
  } catch {
    return fallback;
  }
  return fallback;
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

function mount(model: ReturnType<typeof createModel>) {
  let pending = false;
  let validationErrors: ValidationError[] = [];
  let validationStarted = false;
  const drafts = new Map<string, string>();

  function act(...[control, argument]:
    | [control: Extract<Control, { kind: 'button' }>]
    | [control: Extract<Control, { kind: 'choice' }>, argument: string]
    | [control: Extract<Control, { kind: 'editor' }>, argument: Value]
  ) {
    if (pending) return;
    try {
      if (drafts.size > 0 && (control.kind === 'choice' ||
        (control.kind === 'button' && control.effect.kind !== 'appendDefault'))) {
        announce('Apply your edits before using this control.', true);
        render(drafts.keys().next().value);
        return;
      }
      model.apply(control.key, argument);
      validationErrors = validationStarted ? model.errors() : [];
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
      const path = node && (node.kind === 'actionWidget' && node.children.some(child => child.kind === 'editor') ? null
        : 'location' in node ? node.location : null);
      if (path && rendered instanceof HTMLElement) {
        const messages = validationErrors.filter(error => error.targets.kind === 'locations' &&
          error.targets.locations.some(location => sameLocation(location, path))).map(error => error.message);
        if (messages.length > 0) {
          const feedback = element('p', [...new Set(messages)].join('\n'), 'validation-error');
          feedback.id = `validation-error-${errorId++}`;
          rendered.append(feedback);
          const inputs = node.kind === 'editor' || node.kind === 'choice' ? rendered.querySelectorAll('input, select') : [];
          for (const input of inputs) {
            input.setAttribute('aria-invalid', 'true');
            const describedBy = input.getAttribute('aria-describedby');
            input.setAttribute('aria-describedby', [describedBy, feedback.id].filter(Boolean).join(' '));
          }
        }
      }
      return rendered;
    }
    function renderContent(node: View | null): HTMLElement | DocumentFragment {
      if (!node) return document.createDocumentFragment();
      if (node.kind === 'stack' || node.kind === 'actionWidget') {
        const group = node.label
          ? element('fieldset', undefined, 'component')
          : element('div', undefined, 'stack');
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
        if (node.items.length === 0) group.append(element('p', 'No items.', 'empty'));
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
        wrapper.tabIndex = 0;
        wrapper.setAttribute('role', 'region');
        wrapper.setAttribute('aria-label', 'Table');
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
        if (node.rows.length === 0 && node.columns.length > 0) {
          const row = element('tr');
          const cell = element('td', 'No rows.', 'empty');
          cell.colSpan = node.columns.length;
          row.append(cell);
          body.append(row);
        }
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
      if (node.kind !== 'editor') return unsupported(node);
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
          if (typeof node.value !== 'boolean') throw new Error('Checkbox requires a boolean value.');
          input.checked = node.value;
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
        default: return unsupported(node.widget);
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
    if (pending) return;
    if (drafts.size > 0) {
      announce('Apply your edits before submitting.', true);
      render(drafts.keys().next().value);
      return;
    }
    validationStarted = true;
    validationErrors = model.errors();
    if (validationErrors.length > 0) {
      announce(validationErrors.map(error => error.targets.kind === 'invalidTarget'
        ? 'Invalid validation target: ' + error.message : error.message).join('\n'), true);
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
        const error = await submissionError(response);
        if (error.kind === 'validation') validationErrors = error.errors;
        throw new Error(error.message);
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
    validationErrors = [];
    validationStarted = false;
    model.reset();
    result.hidden = true;
    announce('Started over.');
    render();
  });

  render();
}

try {
  const response = await fetch('/api/form');
  if (!response.ok) throw new Error('Could not load the form.');
  const spec = await response.json() as Specification;
  const title = ('label' in spec.form && spec.form.label) || 'Form';
  required('#title', HTMLElement).textContent = title;
  document.title = `Lean Forms · ${title}`;
  const useWasm = new URLSearchParams(location.search).get('evaluator') === 'wasm';
  const evaluator = useWasm ? await (await import('./wasm.js')).loadWasmEvaluator() : undefined;
  mount(createModel(spec, evaluator));
  container.dataset.evaluator = useWasm ? 'wasm' : 'typescript';
  performance.mark('forms-ready');
  performance.measure('forms-startup', { start: 0, end: 'forms-ready' });
} catch (error) {
  container.setAttribute('aria-busy', 'false');
  count.textContent = '';
  announce(message(error), true);
}
