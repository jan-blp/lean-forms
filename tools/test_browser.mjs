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
        const edit = (label, value) => {
          const form = [...document.querySelectorAll('.editor')].find(form => form.querySelector('label').firstChild.textContent === label);
          const input = form.querySelector('input');
          input.value = value; input.dispatchEvent(new Event('input')); form.requestSubmit();
        };
        await wait(() => document.querySelector('#submit')?.disabled === false);
        check(crossOriginIsolated, 'Shared-memory runtime requires cross-origin isolation');
        check(document.querySelector('[data-runtime=compiled]'), 'Compiled form runtime was not loaded');
        ${body}
        document.querySelector('#submit').click();
        await wait(() => document.querySelector('#status').textContent === 'Submitted successfully.');
        return JSON.parse(document.querySelector('#result pre').textContent);
      })()` });
      assert.notEqual(result.type, 'exception', JSON.stringify(result.exceptionDetails));
      await checkLayout();
      console.log(`PASS: ${name} browser controls, layout, and server validation`);
    } finally { await stop(process); }
  }
  await example('person', `
    const field = label => [...document.querySelectorAll('.editor')].find(form =>
      form.querySelector('label').firstChild.textContent === label);
    const originalName = field('Name').querySelector('input');
    originalName.focus();
    originalName.value = '<img src=x> Grace';
    originalName.dispatchEvent(new Event('input'));
    check(field('Name').querySelector('input') === originalName && document.activeElement === originalName,
      'Draft replaced the editor or lost focus');
    document.querySelector('#submit').click();
    check(document.querySelector('#status').textContent === 'Apply your edits before submitting.',
      'Submitted an unapplied draft');
    field('Name').requestSubmit();
    check(!document.querySelector('#controls img'), 'Name interpreted as HTML');
    document.querySelector('#reset').click();
    check(field('Name').querySelector('input').value === 'Ada', 'Reset kept edit');
    const text = () => document.body.textContent;
    check(text().includes('Ada, age 20'), 'Missing computed summary');
    check(!field('Street'), 'Hidden nested field rendered');
    edit('Name', 'Grace');
    check(text().includes('Grace, age 20'), 'Computed summary did not update');
    document.querySelector('input[type=checkbox]').click();
    check(field('Street').querySelector('input').value === 'Lambda Lane', 'Missing nested value');
    edit('Age', '17');
    check(field('Street').querySelector('input').disabled, 'Dependent field not disabled');
    check(text().includes('Delivery details require an adult.'), 'Dependent text did not update');
    edit('Age', '150');
    document.querySelector('#submit').click();
    await wait(() => document.querySelector('#status').textContent === 'Age must be at most 120.');
    check(field('Age').querySelector('input').getAttribute('aria-invalid') === 'true', 'Missing age feedback');
    edit('Age', '20');
    edit('Street', '');
    document.querySelector('#submit').click();
    await wait(() => document.querySelector('#status').textContent === 'Enter your delivery street.');
    check(field('Street').querySelector('input').getAttribute('aria-invalid') === 'true', 'Missing nested feedback');
    edit('Street', 'Campus');
    edit('Age', '17');
    document.querySelector('#submit').click();
    await wait(() => document.querySelector('#status').textContent === 'Campus delivery requires an adult.');
    edit('Age', '21');
    const originalFetch = window.fetch;
    let finish;
    let posts = 0;
    window.fetch = () => { posts++; return new Promise(resolve => { finish = resolve; }); };
    document.querySelector('#submit').click();
    document.querySelector('#submit').dispatchEvent(new Event('click'));
    document.querySelector('#reset').dispatchEvent(new Event('click'));
    check(posts === 1, 'Duplicate submission while pending');
    finish(new Response(null, { status: 204 }));
    await wait(() => document.querySelector('#status').textContent === 'Submitted successfully.');
    check(field('Age').querySelector('input').value === '21', 'Reset ran while pending');
    window.fetch = originalFetch;
    const forged = await fetch('/api/submit', { method: 'POST', headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ form: 'person', value: { name: 'Forged', age: 150,
        delivery: false, address: { street: 'Campus' } } }) });
    check(forged.status === 422, 'Server accepted an invalid model');
    check((await forged.json()).error.message === 'Age must be at most 120.', 'Server validation did not run');
  `);

} finally {
  socket?.close();
  await Promise.all([stop(firefox), stop(server)]);
  await rm(profile, { recursive: true, force: true });
}
