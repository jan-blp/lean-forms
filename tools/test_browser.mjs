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
      await fetch(`http://127.0.0.1:${port}/api/form`);
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
  await call('browsingContext.navigate', { context, url: `http://127.0.0.1:${port}`, wait: 'complete' });
  const result = await call('script.evaluate', { target: { context }, awaitPromise: true, expression: `(async () => {
    const check = (condition, message) => { if (!condition) throw Error(message); };
    const wait = async predicate => {
      for (let i = 0; i < 100; i++) {
        if (predicate()) return;
        await new Promise(resolve => setTimeout(resolve, 50));
      }
      throw Error('Timed out: ' + document.querySelector('#status').textContent);
    };
    const field = name => [...document.querySelectorAll('.editor')].find(form => form.querySelector('label').firstChild.textContent === name);
    const edit = (name, value) => {
      const input = field(name).querySelector('input');
      input.value = value;
      input.dispatchEvent(new Event('input', { bubbles: true }));
    };
    const apply = name => field(name).querySelector('button').click();
    const status = () => document.querySelector('#status').textContent;
    await wait(() => !document.querySelector('#submit').disabled);
    let posts = 0;
    const originalFetch = window.fetch;
    window.fetch = (...args) => { if (args[0] === '/api/submit') posts++; return originalFetch(...args); };
    edit('Name', '<img src=x> Grace');
    edit('Age (18-120)', '35');
    apply('Name');
    check(field('Age (18-120)').querySelector('input').value === '35', 'Applying Name lost the Age draft');
    check(document.querySelector('#count').textContent === '1 action', 'Draft entered history');
    document.querySelector('#submit').click();
    check(posts === 0 && status() === 'Apply your edits before submitting.', 'Submitted unapplied draft');
    check(document.activeElement === field('Age (18-120)').querySelector('input'), 'Draft not focused');
    edit('Age (18-120)', '-1');
    apply('Age (18-120)');
    check(document.querySelector('#count').textContent === '1 action', 'Invalid draft applied');
    edit('Age (18-120)', '35');
    field('Age (18-120)').requestSubmit();
    document.querySelector('input[type=checkbox]').click();
    const select = document.querySelector('select');
    select.value = '2'; select.dispatchEvent(new Event('change'));
    document.querySelector('#submit').click();
    await wait(() => status() === 'Submitted successfully.');
    const submitted = JSON.parse(document.querySelector('#result pre').textContent);
    check(submitted.name === '<img src=x> Grace' && submitted.age === '35' && submitted.address.kind === 2, 'Wrong submitted value');
    check(!document.querySelector('#result img'), 'Value interpreted as HTML');
    edit('Age (18-120)', '17'); apply('Age (18-120)');
    document.querySelector('#submit').click();
    await wait(() => status() === 'Invalid replayed value');
    check(!document.querySelector('#submit').disabled, 'Rejected submission left controls disabled');
    edit('Age (18-120)', '36'); apply('Age (18-120)');
    document.querySelector('#submit').click();
    await wait(() => status() === 'Submitted successfully.');
    edit('Name', 'Discard me');
    document.querySelector('#reset').click();
    check(field('Name').querySelector('input').value === 'Ada', 'Reset kept draft');
    check(document.querySelector('#count').textContent === '0 actions', 'Reset kept history');
    document.querySelector('#submit').click();
    await wait(() => status() === 'Submitted successfully.');
    check(posts === 4, 'Wrong number of submissions');
    return 'PASS: Apply/Enter, drafts, validation, typed submission, reset';
  })()` });
  assert.notEqual(result.type, 'exception', JSON.stringify(result.exceptionDetails));
  console.log(result.result.value);
  async function example(name, body) {
    const examplePort = await freePort();
    const process = spawn('.lake/build/bin/forms-web', [name, '--port', String(examplePort)], { cwd, stdio: 'ignore' });
    try {
      let ready = false;
      for (let attempt = 0; attempt < 100; attempt++) {
        try { await fetch(`http://127.0.0.1:${examplePort}/api/form`); ready = true; break; }
        catch { await delay(50); }
      }
      assert.ok(ready, `Server did not start: ${name}`);
      await call('browsingContext.navigate', { context, url: `http://127.0.0.1:${examplePort}`, wait: 'complete' });
      const result = await call('script.evaluate', { target: { context }, awaitPromise: true, expression: `(async () => {
        const check = (condition, message) => { if (!condition) throw Error(message); };
        const wait = async predicate => {
          for (let i = 0; i < 100; i++) { if (predicate()) return; await new Promise(resolve => setTimeout(resolve, 50)); }
          throw Error(document.querySelector('#status').textContent || 'Timeout');
        };
        const button = label => [...document.querySelectorAll('button')].find(button => button.textContent === label);
        const edit = (label, value) => {
          const form = [...document.querySelectorAll('.editor')].find(form => form.querySelector('label').firstChild.textContent === label);
          const input = form.querySelector('input');
          input.value = value; input.dispatchEvent(new Event('input')); form.requestSubmit();
        };
        const select = (label, value) => {
          const input = [...document.querySelectorAll('label')].find(node => node.firstChild.textContent === label).querySelector('select');
          input.value = value; input.dispatchEvent(new Event('change'));
        };
        await wait(() => !document.querySelector('#submit').disabled);
        ${body}
        document.querySelector('#submit').click();
        await wait(() => document.querySelector('#status').textContent === 'Submitted successfully.');
        return JSON.parse(document.querySelector('#result pre').textContent);
      })()` });
      assert.notEqual(result.type, 'exception', JSON.stringify(result.exceptionDetails));
      console.log(`PASS: ${name} browser controls and server replay`);
    } finally { await stop(process); }
  }
  await example('invoice', `
    button('Add item').click();
    check(document.querySelectorAll('.list-item').length === 2, 'Append failed');
    const quantity = [...document.querySelectorAll('.editor')].filter(form => form.querySelector('label').firstChild.textContent === 'Quantity')[1];
    const input = quantity.querySelector('input'); input.value = '7'; input.dispatchEvent(new Event('input'));
    button('Remove item').click();
    check(document.querySelectorAll('.list-item').length === 2, 'Removal accepted pending draft');
    const pending = [...document.querySelectorAll('.editor')].filter(form => form.querySelector('label').firstChild.textContent === 'Quantity')[1];
    pending.requestSubmit();
    button('Remove item').click();
    check(document.querySelectorAll('.list-item').length === 1, 'Remove failed');
    check([...document.querySelectorAll('.computed output')].at(-1).textContent === '700', 'Total did not update');
    edit('Description', '<b>literal</b>');
  `);
  await example('shapes', `
    select('Shape', 'rectangle'); edit('Width', '8');
    select('Shape', 'dot'); check(!document.querySelector('input'), 'Inactive payload remains');
    select('Shape', 'rectangle');
    check(document.querySelector('input').value === '4', 'Old payload was restored');
    edit('Height', '7');
  `);
  await example('location', `select('Country', 'Japan'); select('City', '2');`);
  await example('report', `
    check(document.querySelectorAll('tbody tr').length === 4, 'Missing table rows');
    document.querySelector('input[type=checkbox]').click();
    check(document.querySelectorAll('tbody tr').length === 2, 'Filter did not update table');
    select('Sort', '1');
  `);
  await example('basket', `
    check(document.querySelector('table'), 'Missing catalogue');
    const search = [...document.querySelectorAll('.editor')].find(form => form.querySelector('label').firstChild.textContent === 'Search');
    search.querySelector('input').value = 'pen'; search.querySelector('input').dispatchEvent(new Event('input'));
    button('Add selected product').click();
    check(document.querySelector('#count').textContent === '0 actions', 'Action accepted pending draft');
    edit('Search', 'pen');
    button('Add selected product').click();
    select('Page', '1');
    check(document.querySelector('table'), 'Missing basket table');
    check(document.querySelectorAll('tbody tr').length === 3, 'Append did not update basket');
  `);

} finally {
  socket?.close();
  await Promise.all([stop(firefox), stop(server)]);
  await rm(profile, { recursive: true, force: true });
}
