// Browser-only behavior: Wasm under cross-origin isolation, React drafts and focus, escaping, layout.
// Validation rules live in web/compiled.test.mjs and tools/test_web.py.
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
/** Retries `attempt` until it resolves or `ms` elapse, failing early if `process` cannot spawn. */
async function retry(what, process, ms, attempt) {
  let spawnError;
  process.once('error', error => { spawnError = error; });
  const deadline = Date.now() + ms;
  for (;;) {
    if (spawnError) throw spawnError;
    try { return await attempt(); }
    catch (error) { if (Date.now() > deadline) throw new Error(`${what} did not start`, { cause: error }); }
    await delay(100);
  }
}

const debugPort = await freePort();
const profile = await mkdtemp(join(tmpdir(), 'forms-firefox-'));
const firefox = spawn('firefox', ['--headless', '--no-remote', '--profile', profile,
  '--remote-debugging-port', String(debugPort)], { stdio: 'ignore' });
let socket;
try {
  // Cold Firefox on CI can take over 10s.
  socket = await retry('Firefox', firefox, 60000, () => new Promise((resolve, reject) => {
    const candidate = new WebSocket(`ws://127.0.0.1:${debugPort}/session`);
    candidate.onopen = () => resolve(candidate);
    candidate.onerror = reject;
  }));
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
  /** Loads `name` in Firefox, runs `body`, then submits through the real server. */
  async function example(name, body) {
    const port = await freePort();
    const server = spawn('.lake/build/bin/forms-web', [name, '--port', String(port)], { cwd, stdio: 'ignore' });
    try {
      await retry(`Server ${name}`, server, 10000, () => fetch(`http://127.0.0.1:${port}/api/form-start`));
      await call('browsingContext.navigate', { context, url: `http://127.0.0.1:${port}/`, wait: 'complete' });
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
        const input = label => field(label).querySelector('input');
        const edit = async (label, value) => {
          await type(input(label), value);
          field(label).requestSubmit();
          await tick();
        };
        const status = () => document.querySelector('#status').textContent;
        const submitted = () => JSON.parse(document.querySelector('#result pre').textContent);
        await wait(() => document.querySelector('[data-action=submit]')?.disabled === false);
        check(crossOriginIsolated, 'Shared-memory runtime requires cross-origin isolation');
        check(document.querySelector('[data-runtime=compiled]'), 'Compiled form runtime was not loaded');
        ${body}
        await click('[data-action=submit]');
        await wait(() => status() === 'Submitted successfully.');
      })()` });
      assert.notEqual(result.type, 'exception', JSON.stringify(result.exceptionDetails));
      await checkLayout();
      console.log(`PASS: ${name}`);
    } finally { await stop(server); }
  }

  await example('person', `
    const name = input('Name');
    name.focus();
    await type(name, '<img src=x> Grace');
    check(input('Name') === name && document.activeElement === name, 'Draft replaced the editor or lost focus');
    await click('[data-action=submit]');
    await wait(() => status() === 'Submitted successfully.');
    check(submitted().name === '<img src=x> Grace', 'Submit did not apply the draft');
    check(!document.querySelector('#controls img'), 'Name interpreted as HTML');
    const age = input('Age');
    age.focus();
    await type(age, 'abc');
    age.blur();
    await tick();
    check(status() === 'Enter a non-negative whole number.', 'Leaving the field did not apply the edit');
    check(input('Age').value === 'abc', 'Rejected edit lost its draft');
    await edit('Age', '21');
    await click('input[type=checkbox]');
    await type(input('Street'), 'Hidden draft');
    await click('input[type=checkbox]');
    await click('input[type=checkbox]');
    check(input('Street').value === 'Lambda Lane', 'Hidden field kept its draft');
    await edit('Street', '');
    await click('[data-action=submit]');
    await wait(() => input('Street').getAttribute('aria-invalid') === 'true');
    await edit('Street', 'Main');
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
    check(input('Age').value === '21', 'Reset ran while pending');
    window.fetch = originalFetch;
  `);

  await example('order', `
    const choose = async option => {
      [...document.querySelectorAll('.choice input[type=radio]')]
        .find(r => r.parentElement.textContent === option).click();
      await tick();
    };
    // Another branch's draft must not leak into the same slot.
    await type(input('Street'), 'Draft street');
    await choose('Express');
    check(input('Street').value === '' && field('Phone'), 'Express branch did not start fresh');
    await edit('Street', 'Main');
    await edit('City', 'Bern');
    await type(input('Phone'), '079');
    await click('[data-action=submit]');
    await wait(() => status() === 'Submitted successfully.');
    check(submitted().shipping.express.phone === '079', 'Submit did not apply the branch draft');
  `);

  await example('expenses', `
    const rows = () => [...document.querySelectorAll('table tbody tr')];
    const button = (root, label) => [...root.querySelectorAll('button')].find(b => b.textContent === label);
    const select = async index => { button(rows()[index], 'Select').click(); await tick(); };
    const table = document.querySelector('table');
    check(table.caption.textContent === 'Expenses', 'Table caption missing');
    check([...table.querySelectorAll('th')].map(th => th.textContent).join('|') ===
      'Description|Amount (CHF)|Receipt|Actions', 'Table headers changed');
    check(rows().every(row => row.cells.length === 4), 'Table cells lost their columns');
    check(document.body.textContent.includes('CHF 238'), 'Expense total missing');
    check(!field('Description'), 'Details shown without a selection');
    await select(1);
    check(input('Description').value === 'Hotel', 'Selected row details missing');
    check(!document.querySelector('.table-component').contains(field('Description')),
      'Detail editor is still nested in the table component');
    check(rows()[1].getAttribute('aria-selected') === 'true', 'Selected row not marked');
    const description = input('Description');
    description.focus();
    await type(description, 'Hotel Zürich');
    // Selecting another row must save the current draft before changing its editor.
    await select(0);
    check(rows()[1].cells[0].textContent.includes('Hotel Zürich'), 'Switching rows lost the detail draft');
    check(input('Description').value === 'Train to Bern', 'New selection kept the old draft');
    await select(1);
    await type(input('Amount (CHF)'), 'abc');
    await select(0);
    check(rows()[1].getAttribute('aria-selected') === 'true', 'Invalid draft changed selection');
    check(input('Amount (CHF)').value === 'abc', 'Invalid draft was discarded');
    await edit('Amount (CHF)', '200');
    button(rows()[0], 'Remove').click();
    await tick();
    check(rows().length === 1 && rows()[0].getAttribute('aria-selected') === 'true',
      'Removing an earlier row lost selection');
    check(input('Description').value === 'Hotel Zürich', 'Details changed after removing an earlier row');
    button(rows()[0], 'Remove').click();
    await tick();
    check(rows().length === 0 && !field('Description'), 'Removing selected row kept its details');
    check(table.querySelectorAll('th').length === 4, 'Empty table lost headers');
    check(document.querySelector('.empty').textContent === 'No items.', 'Empty table message missing');
    button(document, 'Add expense').click();
    await tick();
    await select(0);
    await edit('Description', 'Lunch');
    await edit('Amount (CHF)', '25');
  `);
} finally {
  socket?.close();
  await stop(firefox);
  await rm(profile, { recursive: true, force: true });
}
