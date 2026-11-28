import { createRoot } from 'react-dom/client';
import { LeanForm, hostWidget, type Wire } from '../../packages/react/src/index.js';

const Unoffered = hostWidget<unknown, { id: string }>(({ onChange }) => <>
  <input type="hidden" />
  <button type="button" className="unoffered" onClick={() => onChange({ id: 'red' })}>Red</button>
</>);

export async function checkHostWidgets() {
  const host = document.createElement('div');
  document.body.append(host);
  const root = createRoot(host);
  const start: Wire.FormStart = await (await fetch('/api/form-start')).json();
  const moduleUrl = new URL('/wasm/forms.mjs', location.href);
  let phase = 'unoffered output';
  const check = (condition: unknown, message: string) => {
    if (!condition) throw new Error(message);
  };
  const wait = async (predicate: () => unknown) => {
    for (let i = 0; i < 100; i++) {
      if (predicate()) return;
      await new Promise(resolve => setTimeout(resolve, 50));
    }
    throw new Error(`Host widget test timed out (${phase}): ${host.textContent}`);
  };
  const accent = () => [...host.querySelectorAll('.computed label')].find(label =>
    label.firstChild?.textContent === 'Chosen accent')?.querySelector('output')?.textContent;
  try {
    root.render(<LeanForm start={start} moduleUrl={moduleUrl} hostWidgets={{ swatchPicker: Unoffered }} />);
    await wait(() => host.querySelector('.unoffered'));
    host.querySelector<HTMLButtonElement>('.unoffered')!.click();
    await wait(() => host.querySelector('.host-widget .validation-error'));
    check(host.querySelector('.host-widget .validation-error')!.textContent ===
      '"red" is not one of the offered colours.' &&
      host.querySelector('.host-widget')!.getAttribute('aria-invalid') === 'true' && accent() === 'blue',
      'An unoffered output reached the model or was not reported');
    phase = 'focus on submit';
    host.querySelector<HTMLButtonElement>('[data-action=submit]')!.click();
    await wait(() => document.activeElement === host.querySelector('.unoffered'));

    phase = 'unregistered host widget';
    root.render(<LeanForm start={{ ...start }} moduleUrl={moduleUrl} hostWidgets={{}} />);
    await wait(() => host.querySelector('[role=alert]'));
    check(host.querySelector('[role=alert]')!.textContent === 'No host widget is registered as "swatchPicker".' &&
      !host.querySelector('.host-widget'), 'An unregistered host widget did not fail the form');
  } finally {
    root.unmount();
    host.remove();
  }
}
