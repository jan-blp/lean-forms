import { createRoot } from 'react-dom/client';
import { LeanForm, type HttpTransport, type Wire } from '../../packages/react/src/index.js';

export async function checkReopen() {
  const host = document.createElement('div');
  document.body.append(host);
  const root = createRoot(host);
  const start: Wire.FormStart = await (await fetch('/api/form-start')).json();
  const moduleUrl = new URL('/wasm/forms.mjs', location.href);
  let calls = 0;
  let phase = 'press before the opening effects';
  const check = (condition: unknown, message: string) => {
    if (!condition) throw new Error(message);
  };
  const wait = async (predicate: () => unknown) => {
    for (let i = 0; i < 100; i++) {
      if (predicate()) return;
      await new Promise(resolve => setTimeout(resolve, 50));
    }
    throw new Error(`Reopen test timed out (${phase}): ${host.textContent}`);
  };
  const transport: HttpTransport = async ({ url, ...request }) => {
    if (url === '/api/account') calls++;
    return fetch(url, request);
  };
  const fill = () => [...host.querySelectorAll('button')].find(button =>
    button.textContent === 'Fill from DB');
  const iban = () => [...host.querySelectorAll('.editor')].find(form =>
    form.querySelector('label')?.firstChild?.textContent === 'IBAN')?.querySelector('input')?.value;
  let pressed = false;
  // `onSnapshot` runs in the same commit as the opening effects, before they are performed.
  const pressOnOpen = () => {
    if (pressed) return;
    pressed = true;
    fill()!.click();
  };
  try {
    root.render(<LeanForm start={start} moduleUrl={moduleUrl} transport={transport}
      onSnapshot={pressOnOpen} />);
    await wait(() => iban() === 'CH93 0076 2011 6238 5295 7');
    check(calls === 1, `Opening the form sent the pending call again (${calls} calls)`);

    phase = 'reopen';
    root.render(<LeanForm start={{ ...start }} moduleUrl={moduleUrl} transport={transport} />);
    await wait(() => iban() === '');
    fill()!.click();
    await wait(() => iban() === 'CH93 0076 2011 6238 5295 7');
    check(calls === 2, `Reopening the form sent ${calls - 1} calls`);
  } finally {
    root.unmount();
    host.remove();
  }
}
