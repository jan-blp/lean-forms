import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { openForm } from '@blp/lean-forms-react/runtime';

const cwd = fileURLToPath(new URL('..', import.meta.url));
execFileSync('lake', ['build', 'Forms.ExampleForms.FormFingerprint'], { cwd, stdio: 'pipe' });
const fixtures = JSON.parse(execFileSync('lake', ['env', 'lean', '--run', 'tools/ExportCompiledForms.lean'], {
  cwd, encoding: 'utf8', maxBuffer: 16 * 1024 * 1024,
}));
const fixture = name => fixtures.find(f => f.start.form === name);

const moduleUrl = new URL('./dist/wasm/forms.mjs', import.meta.url);
const open = start => openForm(start, moduleUrl);
function snapshot(model) { return model.snapshot(); }
const page = model => model.snapshot().view.page;
const submitButton = model => page(model).toolbar.find(c => c.button.onClick === 'submit').button;
const status = model => { const notice = page(model).notice; return (notice.error ?? notice.info).message; };
const result = model => page(model).result;
/** Field error messages in a component tree. */
const messages = value => !value || typeof value !== 'object' ? [] :
  [...(typeof value.error === 'string' ? [value.error] : []), ...Object.values(value).flatMap(messages)];
for (const { start, initial, cases } of fixtures) {
  test(`compiled ${start.form} matches native Lean through actions, views, validation, and reset`, async () => {
    const model = await open(start);
    try {
      assert.deepEqual(snapshot(model), initial);
      for (const { action, expected } of cases) {
        model.send({ apply: { key: action.key, argument: action.argument ?? null } });
        assert.deepEqual(snapshot(model), expected);
        model.send('reset');
        // Reset does not resend requests still in flight.
        assert.deepEqual(snapshot(model), { ...initial,
          view: { ...initial.view, page: { ...initial.view.page, notice: { info: { message: 'Started over.' } } } },
          effects: initial.effects.filter(e => 'submit' in e) });
      }
    } finally { model.dispose(); }
  });
}

test('models preserve independent values and reset', async () => {
  const start = fixture('person').start;
  const a = await open({ ...start, value: { ...start.value, age: 25 } });
  const b = await open(start);
  try {
    const key = a.snapshot().controls.find(c => c.label === 'Age').key;
    a.send({ apply: { key, argument: '30' } });
    assert.equal(a.snapshot().submission.value.age, 30);
    assert.equal(b.snapshot().submission.value.age, 20);
    const copy = a.snapshot().submission; copy.value.age = 0;
    assert.equal(a.snapshot().submission.value.age, 30);
    a.send('reset'); assert.equal(a.snapshot().submission.value.age, 25);
    a.dispose(); a.dispose();
    assert.throws(() => a.send('reset'), /disposed/);
  } finally { a.dispose(); b.dispose(); }
});

test('initialization rejects unknown forms, incompatible revisions, and malformed raw values', async () => {
  const start = fixture('person').start;
  await assert.rejects(open({ ...start, form: 'missing' }), /Unknown compiled form/);
  await assert.rejects(open({ ...start, fingerprint: 'old' }), /version differs/);
  for (const value of [false, {}, { ...start.value, age: '20' }])
    await assert.rejects(open({ ...start, value }));
});

test('hidden and disabled controls reject stale edits', async () => {
  const person = await open(fixture('person').start);
  const order = await open(fixture('order').start);
  const key = (model, label) => model.snapshot().controls.find(c => c.label === label).key;
  const apply = (model, label, argument) => model.send({ apply: { key: key(model, label), argument } });
  try {
    apply(person, 'Request delivery', true);
    const street = key(person, 'Street');
    apply(person, 'Request delivery', false);
    assert.match(person.send({ apply: { key: street, argument: 'Changed' } }).rejection, /unavailable/);
    assert.equal(person.snapshot().submission.value.address.street, 'Lambda Lane');
    const gift = key(order, 'Gift wrap');
    apply(order, 'Quantity', '11');
    assert.match(order.send({ apply: { key: gift, argument: true } }).rejection, /unavailable/);
    assert.equal(order.snapshot().submission.value.gift, false);
  } finally { person.dispose(); order.dispose(); }
});

test('disposed handles stay invalid and rejected requests leave state unchanged', async () => {
  const { createFormRuntime } = await import('../wasm/form-api.mjs');
  const runtime = await createFormRuntime();
  const call = ({ operation, handle, ...fields }) => runtime.form(JSON.stringify(
    operation === 'open' ? { open: { start: fields } } : operation === 'dispose' ? { dispose: { handle } }
      : { send: { handle, event: Object.keys(fields).length ? { [operation]: fields } : operation } }));
  const cycle = () => {
    const opened = call({ operation: 'open', ...fixture('person').start });
    assert.equal(opened.ok, true);
    const { handle, snapshot } = opened.value.opened;
    const key = snapshot.controls.find(c => c.label === 'Age').key;
    assert.equal(call({ operation: 'apply', handle, key, argument: '21' }).ok, true);
    assert.equal(call({ operation: 'reset', handle }).ok, true);
    assert.equal(call({ operation: 'dispose', handle }).ok, true);
    assert.equal(call({ operation: 'reset', handle }).ok, false);
    return handle;
  };
  cycle();
  const next = call({ operation: 'open', ...fixture('person').start });
  const { handle, snapshot: initial } = next.value.opened;
  // The prefix must be valid so truncating at NUL would incorrectly succeed.
  for (const text of ['{', '{}', JSON.stringify({ send: { handle, event: 'submit' } }) + '\0'])
    assert.equal(runtime.form(text).ok, false);
  // An outcome nobody waits for changes nothing.
  const unchanged = call({ operation: 'submitted', handle, outcome: { unreachable: { message: 'late' } } });
  assert.deepEqual(unchanged.value.updated.snapshot, initial);
  const stale = call({ operation: 'apply', handle, key: 'missing', argument: null }).value.updated.snapshot;
  assert.ok(stale.rejection);
  assert.deepEqual(stale.submission, initial.submission);
  assert.equal(call({ operation: 'dispose', handle }).ok, true);
});

test('editor normalization preserves whitespace, types, and natural precision', async () => {
  const model = await open(fixture('person').start);
  const edit = (label, argument) => model.send({ apply: {
    key: model.snapshot().controls.find(c => c.label === label).key, argument } });
  try {
    for (const code of [9, 10, 11, 12, 13, 32, 160, 0x1680,
      ...Array.from({ length: 11 }, (_, i) => 0x2000 + i), 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff]) {
      const c = String.fromCodePoint(code);
      edit('Age', c + '00042' + c);
      assert.equal(model.snapshot().submission.value.age, 42);
    }
    for (const raw of ['', ' ', '-1', '+1', '1.5', '1e3', '0x10', '1 2', '1_000', '_1', '1_', '١', '１',
      '\u00851', '\u180e1', '\u200b1', '1\0']) {
      const before = model.snapshot().submission;
      assert.ok(edit('Age', raw).rejection);
      assert.deepEqual(model.snapshot().submission, before);
    }
    for (const raw of [1, false, null, undefined, {}, []]) {
      const before = model.snapshot();
      assert.throws(() => edit('Age', raw));
      assert.deepEqual(model.snapshot(), before);
    }
    edit('Age', '123456789012345678901234567890');
    assert.ok(JSON.stringify(model.snapshot().view).includes('123456789012345678901234567890'));
    edit('Name', ' 🌍\0 ');
    assert.equal(model.snapshot().submission.value.name, ' 🌍\0 ');
    assert.throws(() => edit('Name', 1));
    for (const raw of ['true', 1, 0, null]) assert.throws(() => edit('Request delivery', raw));
    assert.ok(model.send({ apply: { key: 'missing', argument: null } }).rejection);
  } finally { model.dispose(); }
});

test('Wasm exposes only the compiled-form API and recovers using a fresh instance after a trap', async () => {
  const { readFileSync } = await import('node:fs');
  const binary = readFileSync(new URL('../.lake/wasm/forms.wasm', import.meta.url));
  const exports = WebAssembly.Module.exports(await WebAssembly.compile(binary)).map(e => e.name);
  for (const name of ['forms_init', 'forms_request']) assert.ok(exports.includes(name));
  assert.ok(!exports.some(name => /json_(run|evaluate|check|normalize|validate)/.test(name)));
  const { createFormRuntime } = await import('../wasm/form-api.mjs');
  const trapped = await createFormRuntime();
  assert.throws(() => trapped.form('['.repeat(200000) + ']'.repeat(200000)), /stack overflow|maximum call stack size exceeded/i);
  const fresh = await createFormRuntime();
  const result = fresh.form(JSON.stringify({ open: { start: fixture('person').start } }));
  assert.equal(result.ok, true);
  assert.equal(result.value.opened.snapshot.submission.value.age, 20);
  assert.equal(fresh.form(JSON.stringify({ dispose: { handle: result.value.opened.handle } })).ok, true);
});


test('Lean owns validation visibility, server feedback, and recovery', async () => {
  const model = await open(fixture('person').start);
  try {
    const quantity = model.snapshot().controls.find(c => c.label === 'Age');
    model.send({ apply: { key: quantity.key, argument: '150' } });
    assert.ok(model.snapshot().errors.length);
    assert.deepEqual(messages(model.snapshot().view), []);
    assert.equal(model.snapshot().summary, '');
    model.send('submit');
    assert.deepEqual(model.snapshot().effects, []);
    assert.equal(model.snapshot().submissionBlocked, true);
    assert.ok(messages(model.snapshot().view).length);
    assert.ok(model.snapshot().summary);
    model.send({ apply: { key: quantity.key, argument: '2' } });
    assert.deepEqual(messages(model.snapshot().view), []);
    assert.equal(model.snapshot().submissionBlocked, false);
    const location = quantity.location.map(step => ({ ...step, ignored: true }));
    const error = { message: '<b>Literal 🌍</b>', targets: { kind: 'locations', locations: [location] } };
    const reject = (status, body) => {
      model.send('submit');
      model.send({ submitted: { outcome: { response: { status, body } } } });
    };
    reject(422, JSON.stringify({ error: { kind: 'validation', message: 'Server rejected',
      errors: [error, error, { message: 'Global', targets: { kind: 'global' } }] } }));
    assert.deepEqual(messages(model.snapshot().view), ['<b>Literal 🌍</b>']);
    assert.equal(model.snapshot().summary, 'Server rejected');
    assert.equal(model.snapshot().submissionBlocked, true);
    assert.ok(model.send({ apply: { key: 'missing', argument: null } }).rejection);
    assert.deepEqual(messages(model.snapshot().view), ['<b>Literal 🌍</b>']);
    assert.equal(model.snapshot().summary, 'Server rejected');
    model.send({ apply: { key: quantity.key, argument: '3' } });
    assert.deepEqual(messages(model.snapshot().view), []);
    assert.equal(model.snapshot().summary, '');
    for (const body of ['not json', '{}', JSON.stringify({ error: { kind: 'validation', message: 'Bad',
      errors: [error, { message: 'Broken', targets: { kind: 'locations', locations: [[{kind: 'item', index: '-1'}]] } }] } })]) {
      reject(503, body);
      assert.equal(model.snapshot().summary, 'Submission failed (HTTP 503).');
      assert.deepEqual(messages(model.snapshot().view), []);
    }
    model.send('reset');
    assert.equal(model.snapshot().summary, '');
    model.send({ apply: { key: quantity.key, argument: '150' } });
    assert.deepEqual(messages(model.snapshot().view), []);
    model.send('submit');
    assert.equal(model.snapshot().submissionBlocked, true);
  } finally { model.dispose(); }
});

test('Lean owns submission effects, pending locks, and reset', async () => {
  const model = await open(fixture('person').start);
  try {
    const editor = model.snapshot().controls.find(c => c.label === 'Age');
    const send = (event, fields = {}) => model.send(event === 'submit' || event === 'reset' ? event : { [event]: fields });
    const respond = (status, body) => send('submitted', { outcome: { response: { status, body } } });
    send('apply', { key: editor.key, argument: '07' });
    assert.equal(model.snapshot().submission.value.age, 7);
    send('submit');
    assert.equal((model.snapshot().effects.length > 0), true);
    const submission = model.snapshot().submission;
    const [{ submit: { request: effect } }] = model.snapshot().effects;
    assert.equal(effect.url, '/api/submit');
    assert.equal(effect.method, 'POST');
    assert.equal(effect.headers['Content-Type'], 'application/json');
    assert.deepEqual(JSON.parse(effect.body), submission);
    for (const [event, fields] of [['submit', {}], ['reset', {}], ['apply', { key: editor.key, argument: '8' }]]) {
      send(event, fields);
      assert.equal(model.snapshot().rejection, event === 'apply' ? 'Submission is in progress.' : null);
      assert.equal(submitButton(model).disabled, true);
      assert.equal(page(model).busy, true);
      assert.equal((model.snapshot().effects.length > 0), false);
      assert.deepEqual(model.snapshot().submission, submission);
    }
    send('submitted', { outcome: { unreachable: { message: 'Network offline' } } });
    assert.equal(submitButton(model).disabled, false);
    assert.equal(status(model), 'Network offline');
    send('submit');
    respond(503, 'malformed');
    assert.equal(status(model), 'Submission failed (HTTP 503).');
    assert.equal(submitButton(model).disabled, false);
    send('submit');
    respond(200, '');
    assert.equal(JSON.parse(result(model)).age, 7);
    assert.equal('error' in page(model).notice, false);
    respond(500, '');
    assert.equal(status(model), 'Submitted successfully.');
    send('apply', { key: editor.key, argument: '8' });
    assert.equal(result(model), null);
    assert.equal(model.snapshot().submission.value.age, 8);
    send('reset');
    assert.equal(model.snapshot().submission.value.age, 20);
    send('submit');
    assert.equal((model.snapshot().effects.length > 0), true);
  } finally { model.dispose(); }
});

test('UI state stays local to each model', async () => {
  const a = await open(fixture('person').start);
  const b = await open(fixture('person').start);
  try {
    const checkbox = a.snapshot().controls.find(c => c.widget === 'checkbox');
    a.send({ apply: { key: checkbox.key, argument: true } });
    a.send('submit');
    assert.equal((a.snapshot().effects.length > 0), true);
    assert.equal(submitButton(b).disabled, false);
    assert.equal(b.snapshot().effects.length, 0);
    a.send({ submitted: { outcome: { unreachable: { message: 'Offline' } } } });
    assert.equal(status(a), 'Offline');
    assert.equal(status(b), '');
  } finally { a.dispose(); b.dispose(); }
});

test('rejected applies announce an error and leave the value unchanged', async () => {
  const model = await open(fixture('person').start);
  try {
    const age = model.snapshot().controls.find(c => c.label === 'Age');
    model.send({ apply: { key: age.key, argument: 'abc' } });
    assert.equal('error' in page(model).notice, true);
    assert.equal(model.snapshot().rejection, 'Enter a non-negative whole number.');
    assert.equal(model.snapshot().submission.value.age, 20);
    model.send({ apply: { key: age.key, argument: '21' } });
    assert.equal(model.snapshot().rejection, null);
    assert.equal('error' in page(model).notice, false);
  } finally { model.dispose(); }
});

test('order chooses shipping branches, nests visibility, and validates, alongside person in one runtime', async () => {
  const order = await open(fixture('order').start);
  const person = await open(fixture('person').start);
  const control = label => order.snapshot().controls.find(c => c.label === label);
  const apply = (label, argument) => order.send({ apply: { key: control(label).key, argument } });
  const submit = () => order.send('submit');
  const outputs = () => JSON.stringify(page(order).body);
  const draftLabels = () => order.snapshot().controls
    .filter(c => order.snapshot().draftFields.includes(c.key)).map(c => c.label);
  const shipping = () => order.snapshot().submission.value.shipping;
  try {
    assert.equal(person.snapshot().title, 'Person');
    apply('Quantity', '100');
    apply('Unit price (CHF)', '1234');
    assert.match(outputs(), /CHF 123'400/);
    assert.equal(control('Gift wrap').disabled, true);
    apply('Quantity', '3');
    apply('Gift wrap', true);
    assert.equal(draftLabels().includes('Gift message'), true);
    assert.doesNotMatch(outputs(), /Card preview/);
    submit();
    assert.deepEqual(messages(order.snapshot().view), ['Enter a gift message.']);
    apply('Gift message', 'Hi');
    assert.match(outputs(), /\\"Hi\\" from Grace Hopper/);

    assert.equal(control('Shipping').widget, 'choice');
    assert.deepEqual(draftLabels(), ['Customer name', 'Email', 'Quantity', 'Unit price (CHF)', 'Gift message',
      'Street', 'City']);
    apply('Shipping', 'express');
    assert.deepEqual(shipping(), { express: { address: { street: '', city: '' }, phone: '' } });
    assert.match(outputs(), /Next business day/);
    submit();
    // Express checks the phone once its address is valid.
    assert.deepEqual(messages(order.snapshot().view), ['Enter the shipping street.', 'Enter the shipping city.']);
    apply('Street', 'Main');
    apply('City', 'Bern');
    assert.deepEqual(messages(order.snapshot().view), ['Enter a phone number for the courier.']);
    apply('Phone', '079');
    apply('Quantity', '11');
    submit();
    assert.deepEqual(messages(order.snapshot().view), ['Express shipping is limited to 10 items.']);
    apply('Quantity', '3');
    apply('Shipping', 'express');
    assert.equal(shipping().express.phone, '079');
    const beforeRejectedBranch = order.snapshot().submission.value;
    const rejectedBranch = order.send({ apply: { key: control('Shipping').key, argument: 'drone' } });
    assert.match(rejectedBranch.rejection, /branch 'drone' is no longer available/);
    assert.deepEqual(rejectedBranch.submission.value, beforeRejectedBranch);
    apply('Shipping', 'pickup');
    assert.equal(order.snapshot().rejection, null);
    assert.equal(control('Street'), undefined);
    assert.match(outputs(), /Store, Bahnhofstrasse 1/);
    submit();
    assert.equal(JSON.parse(order.snapshot().effects[0].submit.request.body).value.shipping, 'pickup');
    assert.equal(person.snapshot().submission.value.name, 'Ada');
  } finally { order.dispose(); person.dispose(); }
});

test('expenses adds, removes, and validates items', async () => {
  const model = await open(fixture('expenses').start);
  const key = (label, nth = 0) => model.snapshot().controls.filter(c => c.label === label)[nth].key;
  const apply = (label, argument, nth = 0) =>
    model.send({ apply: { key: key(label, nth), argument } });
  const submit = () => model.send('submit');
  const expenses = () => model.snapshot().submission.value.expenses;
  const outputs = () => JSON.stringify(page(model).body);
  try {
    assert.match(outputs(), /CHF 238/);
    apply('Add expense', null);
    assert.deepEqual(expenses().at(-1), { description: '', amount: 0, receipt: false });
    const items = page(model).body[0].group.children[1];
    assert.deepEqual(items.table.headers, ['Description', 'Amount (CHF)', 'Receipt', 'Actions']);
    assert.deepEqual(items.table.rows.map(row => row.label), ['Expense 1', 'Expense 2', 'Expense 3']);
    assert.equal(items.table.rows.every(row => row.cells.length === 4), true);
    assert.equal(items.table.footer.button.label, 'Add expense');
    apply('Select', null, 2);
    assert.ok(model.snapshot().draftFields.includes(key('Description')));
    submit();
    assert.deepEqual(messages(model.snapshot().view), ['Describe the expense.', 'Enter an amount of at least CHF 1.']);
    assert.deepEqual(model.snapshot().errors[0].targets.locations[0],
      [{ kind: 'field', name: 'expenses' }, { kind: 'index', position: 2 }, { kind: 'field', name: 'description' }]);
    apply('Description', 'Taxi');
    apply('Amount (CHF)', '5000');
    // The report limit is checked once every expense is valid.
    assert.deepEqual(messages(model.snapshot().view), ['Attach a receipt for CHF 100 or more.']);
    // Only expenses of CHF 100 or more show a receipt checkbox.
    apply('Receipt attached', true);
    assert.deepEqual(messages(model.snapshot().view), ["A report is limited to CHF 5'000."]);
    apply('Remove', null, 0);
    assert.deepEqual(expenses().map(e => e.description), ['Hotel', 'Taxi']);
    assert.match(outputs(), /CHF 5'180/);
    apply('Remove', null, 1);
    apply('Remove', null, 0);
    assert.deepEqual(expenses(), []);
    submit();
    assert.deepEqual(messages(model.snapshot().view), ['Add at least one expense.']);
    assert.equal(model.snapshot().effects.length, 0);
    model.send('reset');
    assert.equal(expenses().length, 2);
  } finally { model.dispose(); }
});

test('table selection edits the selected item and follows row removal', async () => {
  const model = await open(fixture('expenses').start);
  const independent = await open(fixture('expenses').start);
  const controls = () => model.snapshot().controls;
  const key = (label, nth = 0) => controls().filter(control => control.label === label)[nth].key;
  const send = (key, argument = null) => model.send({ apply: { key, argument } });
  const apply = (label, argument = null, nth = 0) => send(key(label, nth), argument);
  const table = () => page(model).body[0].group.children[1].table;
  const value = () => model.snapshot().submission.value;
  const selection = () => table().rows.findIndex(row => row.selected === true);
  try {
    const first = key('Select');
    const second = key('Select', 1);
    assert.equal(selection(), -1);
    assert.deepEqual(Object.keys(value()).sort(), ['employee', 'expenses']);
    const beforeSelection = value();
    assert.equal(controls().some(control => control.label === 'Description'), false);
    send(second);
    assert.deepEqual(value(), beforeSelection);
    assert.ok(page(independent).body[0].group.children[1].table.rows.every(row => row.selected === false));
    assert.equal(selection(), 1);
    assert.deepEqual(table().rows.map(row => row.selected), [false, true]);
    assert.equal(table().footer.button.label, 'Add expense');
    assert.equal(page(model).body[0].group.children[2].group.label, 'Selected expense');
    const oldDescription = key('Description');
    assert.ok(model.snapshot().draftFields.includes(oldDescription));
    apply('Description', 'Hotel Zürich');
    assert.deepEqual(value().expenses.map(expense => expense.description), ['Train to Bern', 'Hotel Zürich']);
    assert.equal(table().rows[1].cells[0].output.value, 'Hotel Zürich');
    send(first);
    const before = value();
    const rejected = send(oldDescription, 'Stale');
    assert.match(rejected.rejection, /control is no longer shown/);
    assert.deepEqual(value(), before);
    send(second);
    apply('Remove');
    assert.equal(selection(), 0);
    assert.deepEqual(table().rows.map(row => row.selected), [true]);
    assert.equal(table().rows[0].cells[0].output.value, 'Hotel Zürich');
    apply('Amount (CHF)', 'abc');
    assert.match(model.snapshot().rejection, /non-negative whole number/);
    assert.equal(value().expenses[0].amount, 180);
    apply('Amount (CHF)', '200');
    assert.equal(value().expenses[0].amount, 200);
    apply('Remove');
    assert.equal(selection(), -1);
    assert.equal(table().rows.length, 0);
    assert.equal(controls().some(control => control.label === 'Description'), false);
    apply('Add expense');
    assert.equal(selection(), -1);
    apply('Select');
    assert.ok(controls().some(control => control.label === 'Description'));
    model.send('reset');
    assert.equal(selection(), -1);
    assert.equal(table().rows.length, 2);
  } finally { model.dispose(); independent.dispose(); }
});

test('project planner keeps task selections local to each project', async () => {
  const model = await open(fixture('projects').start);
  const value = () => model.snapshot().submission.value;
  const projectRows = () => page(model).body[0].group.children
    .find(component => component.group?.label === 'Projects').group.children.filter(component => component.group);
  const body = index => projectRows()[index].group.children[0].group;
  const table = index => body(index).children.find(component => component.table).table;
  const details = index => body(index).children.find(component => component.group?.label === 'Task details');
  const selected = index => table(index).rows.findIndex(row => row.selected === true);
  const send = (key, argument = null) => model.send({ apply: { key, argument } });
  const field = (label, nth = 0) => model.snapshot().controls.filter(control => control.label === label)[nth].key;
  const buttonKey = button => button.onClick.press.name;
  const rowButton = (project, row, label) => table(project).rows[row].cells.at(-1).group.children
    .find(component => component.button?.label === label).button;
  const select = (project, row) => send(buttonKey(rowButton(project, row, 'Select')));
  const removeProject = index => send(buttonKey(projectRows()[index].group.children
    .find(component => component.button?.label === 'Remove').button));
  const addProject = () => send(field('Add project'));
  try {
    assert.match(JSON.stringify(page(model).body), /2 projects · 5 tasks · 1 complete · 15 h planned/);
    assert.deepEqual([selected(0), selected(1)], [-1, -1]);
    const initialValue = value();
    select(0, 1);
    select(1, 0);
    assert.deepEqual(value(), initialValue);
    assert.deepEqual([selected(0), selected(1)], [1, 0]);
    assert.ok(details(0) && details(1));
    assert.equal(table(0).footer.button.label, 'Add task');
    send(field('Task title'), 'Build keyboard navigation');
    send(field('Completed'), true);
    assert.equal(value().projects[0].tasks[1].title, 'Build keyboard navigation');
    assert.equal(value().projects[1].tasks[0].title, 'Draft the welcome email');
    assert.equal(table(0).rows[1].cells[0].output.value, 'Build keyboard navigation');
    assert.match(JSON.stringify(body(0)), /2 \/ 3 tasks complete/);
    const staleTitle = field('Task title');
    const close = field('Close task');
    const beforeClose = value();
    send(close);
    assert.deepEqual([selected(0), selected(1)], [-1, 0]);
    assert.equal(details(0), undefined);
    assert.ok(details(1));
    assert.deepEqual(value(), beforeClose);
    assert.match(send(close).rejection, /control is no longer shown/);
    assert.match(send(staleTitle, 'Stale').rejection, /control is no longer shown/);
    assert.deepEqual(value(), beforeClose);
    select(0, 1);
    select(1, 1);
    assert.deepEqual([selected(0), selected(1)], [1, 1]);
    removeProject(0);
    assert.equal(value().projects[0].name, 'Customer onboarding');
    assert.equal(selected(0), 1);
    assert.ok(details(0));
    addProject();
    assert.deepEqual([selected(0), selected(1)], [1, -1]);
    assert.equal(details(1), undefined);
    select(1, 0);
    send(field('Task title', 1), 'Plan follow-up');
    send(buttonKey(rowButton(0, 1, 'Remove')));
    assert.deepEqual([selected(0), selected(1)], [-1, 0]);
    assert.equal(details(0), undefined);
    assert.equal(value().projects[1].tasks[0].title, 'Plan follow-up');
    model.send('reset');
    assert.deepEqual(value(), initialValue);
    assert.deepEqual([selected(0), selected(1)], [-1, -1]);
    select(0, 0);
    send(field('Task title'), '');
    model.send('submit');
    assert.deepEqual(messages(model.snapshot().view), ['Give the task a title.']);
    assert.deepEqual(model.snapshot().errors[0].targets.locations[0], [
      { kind: 'field', name: 'projects' }, { kind: 'index', position: 0 },
      { kind: 'field', name: 'tasks' }, { kind: 'index', position: 0 }, { kind: 'field', name: 'title' },
    ]);
    send(field('Task title'), 'Map the new navigation');
    model.send('submit');
    const submitted = JSON.parse(model.snapshot().effects[0].submit.request.body).value;
    assert.deepEqual(Object.keys(submitted).sort(), ['name', 'projects']);
    assert.deepEqual(Object.keys(submitted.projects[0]).sort(), ['name', 'tasks']);
    assert.deepEqual(Object.keys(submitted.projects[0].tasks[0]).sort(), ['completed', 'hours', 'notes', 'owner', 'title']);
  } finally { model.dispose(); }
});
