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
} finally {
  socket?.close();
  await Promise.all([stop(firefox), stop(server)]);
  await rm(profile, { recursive: true, force: true });
}
