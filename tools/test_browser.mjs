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
  async function example(name, body, interact) {
    const port = await freePort();
    const server = spawn('.lake/build/bin/forms-web', [name, '--port', String(port)], { cwd, stdio: 'ignore' });
    try {
      await retry(`Server ${name}`, server, 10000, () => fetch(`http://127.0.0.1:${port}/api/form-start`));
      await call('browsingContext.navigate', { context, url: `http://127.0.0.1:${port}/`, wait: 'complete' });
      const evaluate = async body => {
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
        const submit = async () => {
          await click('[data-action=submit]');
          await wait(() => status() === 'Submitted successfully.');
        };
        await wait(() => document.querySelector('[data-action=submit]')?.disabled === false);
        check(crossOriginIsolated, 'Shared-memory runtime requires cross-origin isolation');
        check(document.querySelector('[data-runtime=compiled]'), 'Compiled form runtime was not loaded');
        ${body}
      })()` });
        assert.notEqual(result.type, 'exception', JSON.stringify(result.exceptionDetails));
      };
      await evaluate(`${body}\nawait submit();`);
      if (interact) await interact(evaluate);
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
    const committedAge = age.value;
    age.focus();
    await type(age, 'abc');
    age.blur();
    await tick();
    check(status() === 'Enter a non-negative whole number.', 'Leaving the field did not apply the edit');
    check(input('Age').value === 'abc', 'Rejected edit lost its draft');
    await type(age, committedAge);
    age.blur();
    await tick();
    check(!field('Age').querySelector('.validation-error'), 'Restoring the value kept a rejected-draft error');
    // Submit applies every draft, then focuses the first problem in rendered order.
    await type(age, 'abc');
    await type(input('Name'), '');
    await click('[data-action=submit]');
    await wait(() => document.activeElement === input('Name'));
    check(input('Age').value === 'abc', 'Submit discarded the rejected draft');
    await edit('Name', 'Grace');
    await edit('Age', committedAge);
    await submit();
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
    let body;
    window.fetch = (_, request) => {
      posts++;
      body = request.body;
      return new Promise(resolve => { finish = resolve; });
    };
    // A second click and a reset before React disables the buttons; Lean must ignore both.
    document.querySelector('[data-action=submit]').click();
    document.querySelector('[data-action=submit]').dispatchEvent(new MouseEvent('click', { bubbles: true }));
    document.querySelector('[data-action=reset]').dispatchEvent(new MouseEvent('click', { bubbles: true }));
    check(posts === 1, 'Duplicate submission while pending');
    finish(new Response(JSON.stringify({ value: JSON.parse(body).value }), { status: 200 }));
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

  await example('navigation', `
    check(!field('Street'), 'Address pane should start unplaced');
    const visit = [...document.querySelectorAll('button')].find(button =>
      button.textContent === 'Go to address problem');
    visit.click();
    await wait(() => field('Street') && document.activeElement === input('Street'));
    visit.focus();
    await type(input('Street'), 'Main');
    check(document.activeElement === visit, 'A draft change replayed the focus effect');
    field('Street').requestSubmit();
    await tick();
    const summary = [...document.querySelectorAll('output')].find(output =>
      output.parentElement.firstChild.textContent === 'Current issues');
    check(summary.textContent === '', 'Issue output did not refresh after editing');
    check(visit.disabled, 'Navigation stayed enabled without an address problem');
    await edit('Street', '');
    check(!visit.disabled, 'Navigation stayed disabled when an address problem returned');
    await click('[data-action=submit]');
    await wait(() => document.activeElement === input('Street'));
    check(summary.textContent === 'Enter your delivery street.', 'Validation issue disappeared');
    await edit('Street', 'Main');
  `);

  await example('scalars', '', async evaluate => {
    const press = keys => call('input.performActions', { context,
      actions: [{ type: 'key', id: 'date-keyboard', actions: [...keys].flatMap(value =>
        [{ type: 'keyDown', value }, { type: 'keyUp', value }]) }] });
    for (const initial of ['2026-11-15', '']) {
      await evaluate(`
        await edit('Paid on', ${JSON.stringify(initial)});
        input('Paid on').focus();
      `);
      await press(initial === '' ? '12' : '\uE003');
      await evaluate(`
        const date = input('Paid on');
        check(date.validity.badInput, 'Date edit was not incomplete');
        const fetch = window.fetch;
        let posts = 0;
        window.fetch = (...args) => { posts++; return fetch(...args); };
        date.form.requestSubmit();
        await tick();
        date.blur();
        await tick();
        await click('[data-action=submit]');
        window.fetch = fetch;
        check(posts === 0, 'Incomplete optional date was submitted');
        check(date.getAttribute('aria-invalid') === 'true' &&
          date.form.querySelector('.validation-error')?.textContent, 'Incomplete date lost its error');
        await edit('Paid on', ${JSON.stringify(initial === '' ? '' : '2026-12-01')});
        await submit();
        check(submitted().paidOn === ${JSON.stringify(initial === '' ? null : '2026-12-01')},
          'Correcting or clearing the date did not save');
        check(!date.hasAttribute('aria-invalid'), 'Date error did not clear');
      `);
    }
    await evaluate("input('Paid on').focus();");
    await press('12');
    await evaluate(`
      const date = input('Paid on');
      check(date.validity.badInput, 'Reset test did not create an incomplete date');
      await click('[data-action=reset]');
      check(date.value === '' && !date.validity.badInput, 'Reset kept the incomplete date');
      await submit();
      check(submitted().paidOn === null, 'Reset date did not submit as absent');
    `);
  });

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
  await example('projects', `
    const projects = () => [...document.querySelectorAll('fieldset')].filter(group =>
      /^Project [0-9]+$/.test(group.querySelector(':scope > legend')?.textContent ?? ''));
    const rows = index => [...projects()[index].querySelectorAll('table tbody tr')];
    const button = (root, label) => [...root.querySelectorAll('button')].find(b => b.textContent === label);
    const select = async (project, row) => { button(rows(project)[row], 'Select').click(); await tick(); };
    const projectField = (index, label) => [...projects()[index].querySelectorAll('.editor')]
      .find(editor => editor.querySelector('label').firstChild.textContent === label);
    const projectInput = (index, label) => projectField(index, label)?.querySelector('input');
    const editIn = async (index, label, value) => {
      await type(projectInput(index, label), value);
      projectField(index, label).requestSubmit();
      await tick();
    };
    check(projects().length === 2, 'Initial projects missing');
    check(document.body.textContent.includes('2 projects · 5 tasks · 1 complete · 15 h planned'),
      'Planner overview missing');
    check(!projectField(0, 'Task title') && !projectField(1, 'Task title'), 'Details shown before selection');
    await select(0, 1);
    await select(1, 0);
    check(projectInput(0, 'Task title').value === 'Build accessible navigation', 'First project selection missing');
    check(projectInput(1, 'Task title').value === 'Draft the welcome email', 'Second project changed the first selection');
    check(!projects()[0].querySelector('.table-component').contains(projectField(0, 'Task title')),
      'Task editor is nested inside the table');
    await type(projectInput(0, 'Task title'), 'Build keyboard navigation');
    await select(1, 1);
    check(rows(0)[1].cells[0].textContent.includes('Build keyboard navigation'), 'Switching projects lost a draft');
    check(projectInput(0, 'Task title').value === 'Build keyboard navigation', 'First project lost its selected task');
    check(projectInput(1, 'Task title').value === 'Measure activation', 'Second project did not switch tasks');
    await type(projectInput(1, 'Estimated hours'), 'oops');
    button(projects()[1], 'Close task').click();
    await tick();
    check(projectInput(1, 'Task title'), 'Close task discarded an invalid draft');
    await select(0, 0);
    check(rows(0)[1].getAttribute('aria-selected') === 'true', 'Invalid draft changed selection');
    check(projectInput(1, 'Estimated hours').value === 'oops', 'Invalid draft was discarded');
    await editIn(1, 'Estimated hours', '4');
    projectInput(0, 'Completed').click();
    await tick();
    check(projects()[0].textContent.includes('2 / 3 tasks complete'), 'Progress did not update');
    await type(projectInput(0, 'Notes'), 'Saved when closing');
    button(projects()[0], 'Close task').click();
    await tick();
    check(!projectField(0, 'Task title'), 'Close task left the editor open');
    check(projectInput(1, 'Task title').value === 'Measure activation', 'Close task affected another project');
    await select(0, 1);
    check(projectInput(0, 'Notes').value === 'Saved when closing', 'Close task lost a draft');
    projects()[0].querySelector(':scope > button').click();
    await tick();
    check(projects().length === 1 && projectInput(0, 'Project name').value === 'Customer onboarding',
      'Removed the wrong project');
    check(projectInput(0, 'Task title').value === 'Measure activation', 'Selection did not follow the project');
    button(document, 'Add project').click();
    await tick();
    check(projects().length === 2 && !projectField(1, 'Task title'), 'New project inherited a selection');
    check(projectInput(0, 'Task title').value === 'Measure activation', 'Adding a project changed an existing selection');
    check(rows(1).length === 0, 'New project should start without tasks');
    button(projects()[1], 'Add task').click();
    await tick();
    await select(1, 0);
    await editIn(1, 'Task title', 'Plan follow-up');
    button(rows(0)[1], 'Remove').click();
    await tick();
    check(!projectField(0, 'Task title') && projectInput(1, 'Task title').value === 'Plan follow-up',
      'Removing a task affected another project');
    await click('[data-action=reset]');
    check(projects().length === 2 && !projectField(0, 'Task title') && !projectField(1, 'Task title'),
      'Reset did not clear project selections');
  `);
  await example('outputs', `
    const output = label => [...document.querySelectorAll('output')].find(element =>
      element.parentElement.firstChild.textContent === label).textContent;
    const press = async label => {
      [...document.querySelectorAll('button')].find(button => button.textContent === label).click();
      await tick();
    };
    await press('Increment');
    check(output('Observer one') === '1' && output('Observer two') === 'Twice: 2', 'Observers did not read the owner output');
    await press('Change private');
    check(output('Private value') === '101' && output('Observer one') === '1', 'Private changes leaked into the output');
    await press('Remember output');
    await press('Increment');
    check(output('Observer one') === '2' && output('Remembered') === '1', 'Output and consumer state were not independent');
    await click('[data-action=reset]');
    check(output('Observer one') === '0' && output('Remembered') === '0' && output('Private value') === '100',
      'Reset did not restore both subtrees');
  `);
  await example('nested-outputs', `
    const output = label => [...document.querySelectorAll('output')].find(element =>
      element.parentElement.firstChild.textContent === label).textContent;
    const press = async (label, index = 0) => {
      [...document.querySelectorAll('button')].filter(button => button.textContent === label)[index].click();
      await tick();
    };
    await press('Increment');
    await press('Increment', 1);
    await press('Increment', 3);
    await press('Increment', 3);
    check(output('Pair totals') === '2, 2' && output('Overall sum') === '4', 'Nested outputs did not reach outer observers');
    await press('Change private', 3);
    check(output('Overall sum') === '4', 'Private child state leaked through the composite output');
    await press('Remove');
    check(output('Pair totals') === '2' && output('Overall sum') === '2', 'Removing a composite lost surviving child state');
    await press('Add pair');
    check(output('Pair totals') === '2, 0', 'New composite did not start with fresh child state');
    await click('[data-action=reset]');
    check(output('Pair totals') === '0, 0', 'Reset did not restore nested outputs');
  `);
  await example('present-table', `
    const output = () => [...document.querySelectorAll('output')].find(element =>
      element.parentElement.firstChild.textContent === 'Selected descriptions').textContent;
    const press = async (label, index = 0) => {
      [...document.querySelectorAll('button')].filter(button => button.textContent === label)[index].click();
      await tick();
    };
    await press('Toggle selection', 1);
    check(output() === 'Bread', 'Second row did not select independently');
    await press('Toggle selection');
    check(output() === 'Apples, Bread', 'Selections were not listed in row order');
    await edit('Description', 'Revised');
    check(output() === 'Revised, Bread', 'Summary did not observe the edited cell output');
    await press('Remove');
    check(output() === 'Bread', 'Removing a row lost the surviving selection');
    await press('Add item');
    check(output() === 'Bread', 'New row inherited a selection');
    await click('[data-action=reset]');
    check(output() === '', 'Reset did not clear row-local selections');
  `);
  await example('evidence', `
    const cell = id => document.querySelector('.cell[data-cell="' + id + '"]');
    const evidence = label => field(label).querySelector('.evidence-status')?.classList[1];
    const pick = async (label, ...cells) => {
      field(label).querySelector('.pick').click();
      await tick();
      check(document.querySelector('.document.picking'), 'Picking did not start');
      for (const id of cells) {
        cell(id).dispatchEvent(new MouseEvent('click', { bubbles: true }));
        await tick();
      }
      await click('[data-pick=fill]');
    };
    check(evidence('Invoice number') === 'linked' && evidence('Issued on') === 'missing' &&
      evidence('Total') === 'stale', 'The initial evidence states were wrong');
    check(!field('Internal note').querySelector('.evidence'), 'A field without evidence offered it');
    input('Total').focus();
    await tick();
    check(cell(19).classList.contains('highlighted') && cell(19).classList.contains('stale'),
      'Focusing the total did not highlight its stale cell');
    const pointer = (type, label) => {
      input(label).dispatchEvent(new MouseEvent(type, { bubbles: true, relatedTarget: null }));
      return tick();
    };
    await pointer('mouseover', 'Invoice number');
    check(cell(4).classList.contains('highlighted') && !cell(19).classList.contains('highlighted'),
      'Hovering the number did not show its cells over the focused total');
    await pointer('mouseout', 'Invoice number');
    check(!cell(4).classList.contains('highlighted') && cell(19).classList.contains('highlighted'),
      'Leaving the number did not return to the focused total');
    await pointer('mouseover', 'Issued on');
    check(cell(19).classList.contains('highlighted'), 'Hovering a field without cells hid the focused total');
    await pointer('mouseout', 'Issued on');
    input('Total').blur();
    await tick();
    check(!cell(19).classList.contains('highlighted'), 'Leaving the total kept its highlight');
    await pick('Issued on', 6);
    await wait(() => input('Issued on').value === '2026-11-03');
    check(evidence('Issued on') === 'linked' && !document.querySelector('.document.picking'),
      'The picked date was not linked');
    input('Total').focus();
    await pick('Total', 19);
    await wait(() => evidence('Total') === 'linked');
    check(input('Total').value === '1234.5', 'The picked total was not filled');
    check(cell(19).classList.contains('highlighted') && !cell(19).classList.contains('stale'),
      'The focused total kept showing its cell as stale after the pick');
    input('Total').blur();
    await pick('Total', 7, 8);
    check(input('Total').value === '1234.5' && evidence('Total') === 'linked' &&
      status().startsWith('Could not read "Customer Example Retail AG"'), 'An unreadable pick changed the total');
    await edit('Invoice number', 'INV-2026-0043');
    check(evidence('Invoice number') === 'stale', 'Editing a picked value did not mark it stale');
    await submit();
    const { page, cellIds, text } = submitted().issuedEvidence;
    check(page === 1 && cellIds.join() === '6' && text === '2026-11-03', 'The picked cells were not submitted');
  `);
  const marker = `const marker = () => document.querySelector('.status-marker');
    const issues = () => [...document.querySelectorAll('output')].find(output =>
      output.parentElement.firstChild.textContent === 'Current issues').textContent;
    const visit = () => [...document.querySelectorAll('button')].find(button =>
      button.textContent === 'Go to issue');`;
  await example('payment-method', `
    ${marker}
    check(marker().classList.contains('attention'), 'A failing check did not ask for attention');
    check(issues() === 'The payment method does not match the receipt.',
      'Issues did not list exactly the failing warning');
    visit().click();
    await wait(() => document.activeElement?.closest('fieldset')?.querySelector('legend')
      ?.firstChild.textContent === 'Expense Payment Method');
    marker().click();
    await tick();
    const checks = document.getElementById(marker().getAttribute('popovertarget'));
    check(checks.matches(':popover-open') && checks.textContent.includes('does not match the receipt'),
      'The marker did not list its checks');
    check([...checks.querySelectorAll('.checks-section')].some(section =>
      section.querySelector('.checks-title').textContent === 'Optional' &&
      section.textContent.includes('Attach the original receipt.')), 'The optional check was not marked optional');
    checks.hidePopover();
    [...document.querySelectorAll('label')].find(label => label.textContent === 'BLP credit card')
      .querySelector('input').click();
    await wait(() => marker().classList.contains('outdated'));
    check(issues() === 'The payment method does not match the receipt.',
      'An outdated failing check left the issues');
    marker().click();
    await tick();
    const changed = [...document.getElementById(marker().getAttribute('popovertarget'))
      .querySelectorAll('.checks-section')].find(section =>
        section.querySelector('.checks-title').textContent.startsWith('Changed since the last check'));
    check([...changed.querySelectorAll('.check')].some(item =>
      item.textContent.includes('Attach the original receipt.') && item.querySelector('.tag')),
      'An outdated optional check was not marked outdated and optional');
    document.getElementById(marker().getAttribute('popovertarget')).hidePopover();
  `, async evaluate => {
    await evaluate(`
      ${marker}
      await wait(() => marker().classList.contains('resolved'));
      check(issues() === '' && visit().disabled, 'A resolved check stayed an issue');
      const button = caption => [...document.querySelectorAll('button')]
        .find(button => button.textContent === caption);
      check(!button('Approve'), 'A passing check offered approval');
      [...document.querySelectorAll('label')].find(label => label.textContent === 'Privately paid')
        .querySelector('input').click();
      await submit();
      await wait(() => marker().classList.contains('attention') && button('Approve'));
      button('Approve').click();
      await wait(() => marker().classList.contains('outdated') && button('Withdraw approval'));
      check(issues() === 'The payment method does not match the receipt.',
        'An approval resolved a check before the server confirmed it');
      await submit();
      await wait(() => marker().classList.contains('resolved'));
      check(issues() === '' && submitted().approved === 'privatelyPaid',
        'The server did not confirm the approval');
      check([...document.getElementById(marker().getAttribute('popovertarget'))
        .querySelectorAll('.checks-section')].some(section =>
          section.querySelector('.checks-title').textContent === 'Approved' &&
          section.textContent.includes('does not match the receipt')),
        'The approved check was not listed as approved');
    `);
    await call('browsingContext.setViewport', { context, viewport: { width: 375, height: 300 } });
    await evaluate(`
      ${marker}
      window.scrollTo(0, 0);
      const panel = document.getElementById(marker().getAttribute('popovertarget'));
      const toggle = () => new Promise(resolve => {
        panel.addEventListener('toggle', resolve, { once: true });
        marker().click();
      });
      const fits = () => {
        const bounds = panel.getBoundingClientRect();
        return bounds.top >= 16 && bounds.bottom <= innerHeight - 16 &&
          bounds.left >= 16 && bounds.right <= innerWidth - 16;
      };
      await toggle();
      check(fits(), 'Checks overflowed a short viewport');
      check(panel.getBoundingClientRect().bottom <= marker().getBoundingClientRect().top,
        'Checks did not open above the marker when space below was limited');
      await toggle();
      const item = panel.querySelector('.check');
      const text = item.textContent;
      item.textContent = text.repeat(50);
      await toggle();
      check(fits() && panel.scrollHeight > panel.clientHeight,
        'Long checks did not fit in a scrollable popover');
      panel.scrollTop = panel.scrollHeight;
      const last = [...panel.querySelectorAll('.check')].at(-1);
      check(last.getBoundingClientRect().bottom <= panel.getBoundingClientRect().bottom,
        'The final check could not be scrolled into view');
      await toggle();
      item.textContent = text;
    `);
  });

} finally {
  socket?.close();
  await stop(firefox);
  await rm(profile, { recursive: true, force: true });
}
