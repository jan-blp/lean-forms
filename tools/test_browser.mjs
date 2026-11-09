// Requires Firefox and Node.js 22+. Run after lake build forms-web.
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { once } from 'node:events';
import { mkdtemp, rm } from 'node:fs/promises';
import { createServer } from 'node:net';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const cwd = fileURLToPath(new URL('..', import.meta.url));

const delay = ms => new Promise(resolve => setTimeout(resolve, ms));
async function freePort() {
  const listener = createServer();
  listener.listen(0, '127.0.0.1');
  await once(listener, 'listening');
  const port = listener.address().port;
  await new Promise(resolve => listener.close(resolve));
  return port;
}
async function stop(process) {
  if (!process.pid || process.exitCode !== null || process.signalCode !== null) return;
  const exited = once(process, 'exit');
  process.kill();
  const timer = setTimeout(() => process.kill('SIGKILL'), 3000);
  try { await exited; } finally { clearTimeout(timer); }
}

const port = await freePort();
const debugPort = await freePort();
const profile = await mkdtemp(join(tmpdir(), 'forms-firefox-'));
const server = spawn('.lake/build/bin/forms-web', ['person', '--port', String(port)], { cwd, stdio: 'ignore' });
const firefox = spawn('firefox', ['--headless', '--no-remote', '--profile', profile,
  '--remote-debugging-port', String(debugPort)], { stdio: 'ignore' });
let startupError;
for (const process of [server, firefox]) process.on('error', error => { startupError = error; });
let socket;
try {
  for (let attempt = 0; attempt < 100; attempt++) {
    if (startupError) throw startupError;
    try {
      await fetch(`http://127.0.0.1:${port}/api/compiled-form`);
      socket = new WebSocket(`ws://127.0.0.1:${debugPort}/session`);
      await new Promise((resolve, reject) => { socket.onopen = resolve; socket.onerror = reject; });
      break;
    } catch { await delay(100); }
  }
  assert.equal(socket?.readyState, WebSocket.OPEN, 'Server/browser did not start');
  let id = 0;
  const pending = new Map();
  socket.onmessage = event => {
    const response = JSON.parse(event.data);
    const request = pending.get(response.id);
    if (!request) return;
    pending.delete(response.id);
    clearTimeout(request.timer);
    response.type === 'error' ? request.reject(new Error(JSON.stringify(response))) : request.resolve(response.result);
  };
  const call = (method, params) => new Promise((resolve, reject) => {
    const requestId = ++id;
    const timer = setTimeout(() => { pending.delete(requestId); reject(new Error(`Timeout: ${method}`)); }, 15000);
    pending.set(requestId, { resolve, reject, timer });
    socket.send(JSON.stringify({ id: requestId, method, params }));
  });
  await call('session.new', { capabilities: {} });
  const { context } = await call('browsingContext.create', { type: 'tab' });
  async function checkLayout() {
    for (const width of [900, 375, 320]) {
      await call('browsingContext.setViewport', { context, viewport: { width, height: 1000 } });
      const result = await call('script.evaluate', { target: { context }, awaitPromise: false,
        expression: 'document.documentElement.scrollWidth <= innerWidth' });
      assert.equal(result.result.value, true, `Horizontal page overflow at ${width}px`);
    }
  }
  async function example(name, body) {
    const examplePort = await freePort();
    const process = spawn('.lake/build/bin/forms-web', [name, '--port', String(examplePort)], { cwd, stdio: 'ignore' });
    try {
      let ready = false;
      for (let attempt = 0; attempt < 100; attempt++) {
        try { await fetch(`http://127.0.0.1:${examplePort}/api/compiled-form`); ready = true; break; }
        catch { await delay(50); }
      }
      assert.ok(ready, `Server did not start: ${name}`);
      await call('browsingContext.navigate', { context, url: `http://127.0.0.1:${examplePort}/`, wait: 'complete' });
      const result = await call('script.evaluate', { target: { context }, awaitPromise: true, expression: `(async () => {
        const check = (condition, message) => { if (!condition) throw Error(message); };
        const wait = async predicate => {
          for (let i = 0; i < 100; i++) { if (predicate()) return; await new Promise(resolve => setTimeout(resolve, 50)); }
          throw Error(document.querySelector('#status').textContent || 'Timeout');
        };
        // React commits after the event; let it render before the next check.
        const tick = () => new Promise(resolve => setTimeout(resolve, 0));
        // React tracks the value setter, so typing must use the native one and a bubbling event.
        const type = async (input, value) => {
          Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, 'value').set.call(input, value);
          input.dispatchEvent(new Event('input', { bubbles: true }));
          await tick();
        };
        const click = async selector => { document.querySelector(selector).click(); await tick(); };
        const field = label => [...document.querySelectorAll('.editor')].find(form =>
          form.querySelector('label').firstChild.textContent === label);
        const edit = async (label, value) => {
          await type(field(label).querySelector('input'), value);
          field(label).requestSubmit();
          await tick();
        };
        await wait(() => document.querySelector('[data-action=submit]')?.disabled === false);
        check(crossOriginIsolated, 'Shared-memory runtime requires cross-origin isolation');
        check(document.querySelector('[data-runtime=compiled]'), 'Compiled form runtime was not loaded');
        ${body}
        await click('[data-action=submit]');
        await wait(() => document.querySelector('#status').textContent === 'Submitted successfully.');
        return JSON.parse(document.querySelector('#result pre').textContent);
      })()` });
      assert.notEqual(result.type, 'exception', JSON.stringify(result.exceptionDetails));
      await checkLayout();
      console.log(`PASS: ${name} browser controls, layout, and server validation`);
    } finally { await stop(process); }
  }
  await example('person', `
    const status = () => document.querySelector('#status').textContent;
    const originalName = field('Name').querySelector('input');
    originalName.focus();
    await type(originalName, '<img src=x> Grace');
    check(field('Name').querySelector('input') === originalName && document.activeElement === originalName,
      'Draft replaced the editor or lost focus');
    await click('[data-action=submit]');
    await wait(() => status() === 'Submitted successfully.');
    check(JSON.parse(document.querySelector('#result pre').textContent).name === '<img src=x> Grace',
      'Submit did not apply the draft');
    check(!document.querySelector('#controls img'), 'Name interpreted as HTML');
    await click('[data-action=reset]');
    check(field('Name').querySelector('input').value === 'Ada', 'Reset kept edit');
    const text = () => document.body.textContent;
    check(text().includes('Ada, age 20'), 'Missing computed summary');
    check(!field('Street'), 'Hidden nested field rendered');
    await edit('Name', 'Grace');
    check(text().includes('Grace, age 20'), 'Computed summary did not update');
    await edit('Age', 'abc');
    check(field('Age').querySelector('input').value === 'abc' && status() === 'Enter a non-negative whole number.',
      'Rejected edit lost its draft');
    await edit('Age', '20');
    await click('input[type=checkbox]');
    check(field('Street').querySelector('input').value === 'Lambda Lane', 'Missing nested value');
    await type(field('Street').querySelector('input'), 'Hidden draft');
    await click('input[type=checkbox]');
    await click('input[type=checkbox]');
    check(field('Street').querySelector('input').value === 'Lambda Lane', 'Hidden field kept its draft');
    await edit('Age', '17');
    check(field('Street').querySelector('input').disabled, 'Dependent field not disabled');
    check(text().includes('Delivery details require an adult.'), 'Dependent text did not update');
    await edit('Age', '150');
    await click('[data-action=submit]');
    await wait(() => status() === 'Age must be at most 120.');
    check(field('Age').querySelector('input').getAttribute('aria-invalid') === 'true', 'Missing age feedback');
    await edit('Age', '20');
    await edit('Street', '');
    await click('[data-action=submit]');
    await wait(() => status() === 'Enter your delivery street.');
    check(field('Street').querySelector('input').getAttribute('aria-invalid') === 'true', 'Missing nested feedback');
    await edit('Street', 'Campus');
    await edit('Age', '17');
    await click('[data-action=submit]');
    await wait(() => status() === 'Campus delivery requires an adult.');
    await edit('Age', '21');
    const originalFetch = window.fetch;
    let finish;
    let posts = 0;
    window.fetch = () => { posts++; return new Promise(resolve => { finish = resolve; }); };
    // A second click and a reset before React disables the buttons; Lean must ignore both.
    document.querySelector('[data-action=submit]').click();
    document.querySelector('[data-action=submit]').dispatchEvent(new MouseEvent('click', { bubbles: true }));
    document.querySelector('[data-action=reset]').dispatchEvent(new MouseEvent('click', { bubbles: true }));
    check(posts === 1, 'Duplicate submission while pending');
    finish(new Response(null, { status: 204 }));
    await wait(() => status() === 'Submitted successfully.');
    check(field('Age').querySelector('input').value === '21', 'Reset ran while pending');
    window.fetch = originalFetch;
    const { fingerprint } = await (await fetch('/api/compiled-form')).json();
    const forged = await fetch('/api/submit', { method: 'POST', headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ form: 'person', fingerprint, value: { name: 'Forged', age: 150,
        delivery: false, address: { street: 'Campus' } } }) });
    check(forged.status === 422, 'Server accepted an invalid model');
    check((await forged.json()).error.message === 'Age must be at most 120.', 'Server validation did not run');
  `);

} finally {
  socket?.close();
  await Promise.all([stop(firefox), stop(server)]);
  await rm(profile, { recursive: true, force: true });
}
