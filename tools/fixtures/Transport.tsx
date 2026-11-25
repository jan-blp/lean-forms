import { createRoot } from 'react-dom/client';
import { LeanForm, type HttpTransport, type Wire } from '../../packages/react/src/index.js';

export async function checkTransport() {
  const host = document.createElement('div');
  document.body.append(host);
  const root = createRoot(host);
  const start: Wire.FormStart = await (await fetch('/api/form-start')).json();
  const moduleUrl = new URL('/wasm/forms.mjs', location.href);
  const calls: { request: Wire.HttpEffect; token: string }[] = [];
  let phase = 'initial lookup';
  const check = (condition: unknown, message: string) => {
    if (!condition) throw new Error(message);
  };
  const wait = async (predicate: () => unknown) => {
    for (let i = 0; i < 100; i++) {
      if (predicate()) return;
      await new Promise(resolve => setTimeout(resolve, 50));
    }
    throw new Error(`Transport test timed out (${phase}): ${host.textContent}; ${JSON.stringify(calls)}`);
  };
  const render = (transport: HttpTransport) => new Promise<void>(resolve => {
    root.render(<LeanForm start={start} moduleUrl={moduleUrl} transport={transport}
      onSnapshot={() => resolve()} />);
  });
  const authenticated = (token: string): HttpTransport => async request => {
    calls.push({ request, token });
    const { url, ...init } = request;
    return fetch(url, { ...init, headers: { ...init.headers, Authorization: `Bearer ${token}` } });
  };
  const country = () => host.querySelector<HTMLInputElement>('input')!;
  const search = async (text: string) => {
    country().focus();
    Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, 'value')!.set!.call(country(), text);
    country().dispatchEvent(new Event('input', { bubbles: true }));
  };
  const choose = async (text: string) => {
    await wait(() => host.querySelector('[role=option]')?.textContent === text);
    host.querySelector<HTMLButtonElement>('[role=option]')!.click();
    await wait(() => country().value === text && !host.querySelector('[role=listbox]'));
  };
  const submit = async () => {
    country().blur();
    await new Promise(resolve => setTimeout(resolve, 0));
    host.querySelector<HTMLButtonElement>('[data-action=submit]')!.click();
  };
  const status = () => host.querySelector('#status')?.textContent;
  try {
    await render(authenticated('first-token'));
    await search('cat');
    await choose('Catalonia');
    check(calls.some(call => call.request.url === '/api/countries' &&
      call.request.body === '"cat"' && call.token === 'first-token'), 'Lookup bypassed the transport');

    await render(authenticated('rotated-token'));
    phase = 'rotated lookup';
    check(country().value === 'Catalonia', 'Changing the transport reset the form');
    await search('ger');
    await choose('Germany');
    check(calls.at(-1)?.token === 'rotated-token', 'Lookup used the previous transport');
    phase = 'submission';
    await submit();
    await wait(() => status() === 'Submitted successfully.');
    const saved = JSON.parse(calls.at(-1)!.request.body!);
    check(saved.value.country.id === 'DE' && calls.at(-1)?.token === 'rotated-token',
      'Submission bypassed the transport or lost the selection');

    await render(async request => {
      calls.push({ request, token: 'unauthorized' });
      return new Response('', { status: 401 });
    });
    phase = 'unauthorized lookup';
    await search('denied');
    await wait(() => host.textContent?.includes('Could not search:'));
    check(!host.querySelector('[role=option]'), 'An unauthorized lookup showed options');
    phase = 'unauthorized submission';
    await submit();
    await wait(() => status()?.includes('HTTP 401'));

    await render(async request => {
      calls.push({ request, token: 'unreachable' });
      throw new Error('Host session unavailable');
    });
    phase = 'unreachable lookup';
    await search('offline');
    await wait(() => host.textContent?.includes('Could not search: Host session unavailable'));
    phase = 'unreachable submission';
    await submit();
    await wait(() => status()?.includes('Host session unavailable'));
  } finally {
    root.unmount();
    host.remove();
  }
}
