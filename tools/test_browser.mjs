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
  async function checkLayout() {
    for (const width of [900, 375, 320]) {
      await call('browsingContext.setViewport', { context, viewport: { width, height: 1000 } });
      const result = await call('script.evaluate', { target: { context }, awaitPromise: false,
        expression: 'document.documentElement.scrollWidth <= innerWidth' });
      assert.equal(result.result.value, true, `Horizontal page overflow at ${width}px`);
    }
  }
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
    await wait(() => status() === 'Attendees must be between 18 and 120 years old.');
    check(!document.querySelector('#submit').disabled, 'Rejected submission left controls disabled');
    const ageInput = field('Age (18-120)').querySelector('input');
    check(ageInput.getAttribute('aria-invalid') === 'true', 'Invalid field not marked');
    check(document.getElementById(ageInput.getAttribute('aria-describedby')).textContent === status(), 'Missing inline feedback');
    check(!field('Name').querySelector('[aria-invalid]'), 'Error attached to unrelated field');
    edit('Age (18-120)', '36'); apply('Age (18-120)');
    check(!document.querySelector('.validation-error, [aria-invalid]'), 'Applied edit kept stale errors');
    document.querySelector('#submit').click();
    await wait(() => status() === 'Submitted successfully.');
    edit('Name', 'Discard me');
    document.querySelector('#reset').click();
    check(field('Name').querySelector('input').value === 'Ada', 'Reset kept draft');
    check(document.querySelector('#count').textContent === '0 actions', 'Reset kept history');
    document.querySelector('#submit').click();
    await wait(() => status() === 'Submitted successfully.');
    check(posts === 3, 'Invalid value reached the server');
    for (const body of ['null', '{"error": {"message": "wrong shape"}}', '<html>Unavailable</html>']) {
      window.fetch = async () => new Response(body, { status: 503 });
      document.querySelector('#submit').click();
      await wait(() => !document.querySelector('#submit').disabled);
      check(status() === 'Submission failed (HTTP 503).', 'Malformed error response was not handled');
    }
    edit('Name', 'Retain me'); apply('Name');
    let finish;
    let pendingPosts = 0;
    window.fetch = () => { pendingPosts++; return new Promise(resolve => { finish = resolve; }); };
    document.querySelector('#submit').click();
    document.querySelector('#submit').dispatchEvent(new Event('click'));
    document.querySelector('#reset').dispatchEvent(new Event('click'));
    const checkbox = document.querySelector('input[type=checkbox]');
    checkbox.dispatchEvent(new Event('change'));
    check(pendingPosts === 1, 'Duplicate submission while pending');
    check(document.querySelector('#count').textContent === '1 action', 'History changed while pending');
    finish(new Response(null, { status: 204 }));
    await wait(() => !document.querySelector('#submit').disabled);
    check(field('Name').querySelector('input').value === 'Retain me', 'Reset ran while pending');
    window.fetch = originalFetch;
    return 'PASS: Apply/Enter, drafts, validation, typed submission, reset, malformed errors, pending guards';
  })()` });
  assert.notEqual(result.type, 'exception', JSON.stringify(result.exceptionDetails));
  console.log(result.result.value);
  await checkLayout();
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
      await checkLayout();
      console.log(`PASS: ${name} browser controls, layout, and server replay`);
    } finally { await stop(process); }
  }
  for (const name of ['counter', 'counters', 'thermostat']) await example(name, '');
  await example('booking', `
    edit('End date (YYYY-MM-DD)', '2028-01-01');
    document.querySelector('#submit').click();
    await wait(() => document.querySelector('#status').textContent === 'End date must be on or after start date.');
    check(document.querySelectorAll('input[aria-invalid="true"]').length === 2, 'Both dates should be marked invalid');
    check(document.querySelectorAll('.validation-error').length === 2, 'Both dates should show feedback');
    edit('End date (YYYY-MM-DD)', '2028-03-01');
    check(!document.querySelector('.validation-error'), 'Correction kept stale feedback');
  `);
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
    button('Remove item').click();
    check(document.querySelector('.empty').textContent === 'No items.', 'Empty list has no explanation');
    button('Add item').click();
  `);
  await example('invoice', `
    button('Add item').click();
    button('Add item').click();
    function quantity(index, value) {
      const editor = [...document.querySelectorAll('.editor')].filter(form => form.querySelector('label').firstChild.textContent === 'Quantity')[index];
      const input = editor.querySelector('input');
      input.value = value; input.dispatchEvent(new Event('input'));
      editor.requestSubmit();
    }
    quantity(1, '0'); quantity(2, '0');
    document.querySelector('#submit').click();
    await wait(() => document.querySelectorAll('input[aria-invalid="true"]').length === 2);
    const items = [...document.querySelectorAll('.list-item')];
    check(!items[0].querySelector('.validation-error'), 'Valid item marked invalid');
    for (const item of items.slice(1)) {
      const invalid = item.querySelectorAll('.editor:has(input[aria-invalid="true"])');
      check(invalid.length === 1 && invalid[0].querySelector('label').firstChild.textContent === 'Quantity', 'Error attached to wrong field');
    }
    quantity(1, '1'); quantity(2, '1');
  `);
  await example('invoice', `
    const originalFetch = window.fetch;
    try {
      window.fetch = async () => new Response(JSON.stringify({ error: {
        kind: 'validation', message: 'List error',
        errors: [{ message: 'List error', targets: { kind: 'locations', locations: [[]] } }],
      } }), { status: 422, headers: { 'Content-Type': 'application/json' } });
      document.querySelector('#submit').click();
      await wait(() => document.querySelector('#status').textContent === 'List error');
      check(document.querySelectorAll('.validation-error').length === 1, 'Missing list feedback');
      check(!document.querySelector('[aria-invalid]'), 'List error marked child fields invalid');
    } finally { window.fetch = originalFetch; }
  `);
  await example('shapes', `
    select('Shape', 'rectangle'); edit('Width', '8');
    select('Shape', 'dot'); check(!document.querySelector('input'), 'Inactive payload remains');
    select('Shape', 'rectangle');
    check(document.querySelector('input').value === '4', 'Old payload was restored');
    edit('Height', '7');
    edit('Width', '0');
    document.querySelector('#submit').click();
    await wait(() => document.querySelector('#status').textContent === 'Size must be at least 1.');
    const width = [...document.querySelectorAll('.editor')].find(form => form.querySelector('label').firstChild.textContent === 'Width');
    const invalid = [...document.querySelectorAll('[aria-invalid="true"]')];
    check(invalid.length === 1 && invalid[0] === width.querySelector('input'), 'Only the width input should be marked invalid');
    check(!document.querySelector('select[aria-invalid]'), 'Constructor selector marked invalid');
    check(document.querySelectorAll('.validation-error').length === 1 && width.querySelector('.validation-error'),
      'Active constructor error did not attach to width');
    edit('Width', '8');
    const originalFetch = window.fetch;
    try {
      window.fetch = async () => new Response(JSON.stringify({ error: {
        kind: 'validation', message: 'Wrong constructor',
        errors: [
          { message: 'Inactive payload', targets: { kind: 'locations', locations: [[{ kind: 'constructor', tag: 'circle' }, { kind: 'field', name: 'width' }]] } },
          { message: 'Untagged payload', targets: { kind: 'locations', locations: [[{ kind: 'field', name: 'value' }, { kind: 'field', name: 'width' }]] } },
        ],
      } }), { status: 422, headers: { 'Content-Type': 'application/json' } });
      document.querySelector('#submit').click();
      await wait(() => document.querySelector('#status').textContent === 'Wrong constructor');
      check(!document.querySelector('.validation-error, [aria-invalid]'),
        'Inactive or untagged payload error attached to active constructor');
    } finally { window.fetch = originalFetch; }
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
    edit('Search', 'no-such-product');
    check(document.querySelector('tbody .empty').textContent === 'No rows.', 'Empty table has no explanation');
    document.querySelector('#reset').click();
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
