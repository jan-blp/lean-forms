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
        assert.deepEqual(snapshot(model), { ...initial, effects: initial.effects.filter(e => 'submit' in e) });
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
    assert.throws(() => a.send('inspect'), /disposed/);
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
    assert.throws(() => person.send({ apply: { key: street, argument: 'Changed' } }), /unavailable/);
    assert.equal(person.snapshot().submission.value.address.street, 'Lambda Lane');
    const gift = key(order, 'Gift wrap');
    apply(order, 'Quantity', '11');
    assert.throws(() => order.send({ apply: { key: gift, argument: true } }), /unavailable/);
    assert.equal(order.snapshot().submission.value.gift, false);
  } finally { person.dispose(); order.dispose(); }
});

test('disposed handles stay invalid and rejected requests leave state unchanged', async () => {
  const { createFormRuntime } = await import('../wasm/form-api.mjs');
  const runtime = await createFormRuntime();
  const call = ({ operation, handle, ...fields }) => runtime.form(JSON.stringify(
    operation === 'open' ? { open: { start: fields } } : operation === 'dispose' ? { dispose: { handle } }
      : { send: { handle, request: Object.keys(fields).length ? { [operation]: fields } : operation } }));
  const cycle = () => {
    const opened = call({ operation: 'open', ...fixture('person').start });
    assert.equal(opened.ok, true);
    const { handle, snapshot } = opened.value.opened;
    const key = snapshot.controls.find(c => c.label === 'Age').key;
    assert.equal(call({ operation: 'apply', handle, key, argument: '21' }).ok, true);
    assert.equal(call({ operation: 'reset', handle }).ok, true);
    assert.equal(call({ operation: 'dispose', handle }).ok, true);
    assert.equal(call({ operation: 'inspect', handle }).ok, false);
    return handle;
  };
  cycle();
  const next = call({ operation: 'open', ...fixture('person').start });
  const handle = next.value.opened.handle;
  const initial = call({ operation: 'inspect', handle });
  // The prefix must be valid so truncating at NUL would incorrectly succeed.
  for (const text of ['{', '{}', JSON.stringify({ send: { handle, request: 'inspect' } }) + '\0'])
    assert.equal(runtime.form(text).ok, false);
  assert.equal(call({ operation: 'apply', handle, key: 'missing', argument: null }).ok, false);
  assert.deepEqual(call({ operation: 'inspect', handle }), initial);
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
      '\u00851', '\u180e1', '\u200b1', '1\0', 1, false, null, undefined, {}, []]) {
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
    assert.throws(() => model.send({ apply: { key: 'missing', argument: null } }));
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
    model.send('validate');
    assert.equal(model.snapshot().submissionBlocked, true);
    assert.ok(messages(model.snapshot().view).length);
    assert.ok(model.snapshot().summary);
    model.send({ apply: { key: quantity.key, argument: '2' } });
    assert.deepEqual(messages(model.snapshot().view), []);
    assert.equal(model.snapshot().submissionBlocked, false);
    const location = quantity.location.map(step => ({ ...step, ignored: true }));
    const error = { message: '<b>Literal 🌍</b>', targets: { kind: 'locations', locations: [location] } };
    model.send({ serverError: { status: 422, body: JSON.stringify({ error: { kind: 'validation', message: 'Server rejected',
      errors: [error, error, { message: 'Global', targets: { kind: 'global' } }] } }) } });
    assert.deepEqual(messages(model.snapshot().view), ['<b>Literal 🌍</b>']);
    assert.equal(model.snapshot().summary, 'Server rejected');
    assert.equal(model.snapshot().submissionBlocked, true);
    const feedback = snapshot(model);
    assert.throws(() => model.send({ apply: { key: 'missing', argument: null } }));
    assert.deepEqual(snapshot(model), feedback);
    model.send({ apply: { key: quantity.key, argument: '3' } });
    assert.deepEqual(messages(model.snapshot().view), []);
    assert.equal(model.snapshot().summary, '');
    for (const body of ['not json', '{}', JSON.stringify({ error: { kind: 'validation', message: 'Bad',
      errors: [error, { message: 'Broken', targets: { kind: 'locations', locations: [[{kind: 'item', index: '-1'}]] } }] } })]) {
      model.send({ serverError: { status: 503, body: body } });
      assert.equal(model.snapshot().summary, 'Submission failed (HTTP 503).');
      assert.deepEqual(messages(model.snapshot().view), []);
    }
    model.send('reset');
    assert.equal(model.snapshot().summary, '');
    model.send({ apply: { key: quantity.key, argument: '150' } });
    assert.deepEqual(messages(model.snapshot().view), []);
    model.send('validate');
    assert.equal(model.snapshot().submissionBlocked, true);
  } finally { model.dispose(); }
});

test('Lean owns submission effects, pending locks, and reset', async () => {
  const model = await open(fixture('person').start);
  try {
    const editor = model.snapshot().controls.find(c => c.label === 'Age');
    const send = (event, fields = {}) => model.send({ event: { message: event === 'submit' || event === 'reset' ? event : { [event]: fields } } });
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
    assert.throws(() => model.send({ apply: { key: editor.key, argument: '8' } }), /progress/);
    assert.throws(() => model.send('reset'), /progress/);
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
    a.send({ event: { message: { apply: { key: checkbox.key, argument: true } } } });
    a.send({ event: { message: 'submit' } });
    assert.equal((a.snapshot().effects.length > 0), true);
    assert.equal(submitButton(b).disabled, false);
    assert.equal(b.snapshot().effects.length, 0);
    a.send({ event: { message: { submitted: { outcome: { unreachable: { message: 'Offline' } } } } } });
    assert.equal(status(a), 'Offline');
    assert.equal(status(b), '');
  } finally { a.dispose(); b.dispose(); }
});

test('rejected applies announce an error and leave the value unchanged', async () => {
  const model = await open(fixture('person').start);
  try {
    const age = model.snapshot().controls.find(c => c.label === 'Age');
    model.send({ event: { message: { apply: { key: age.key, argument: 'abc' } } } });
    assert.equal('error' in page(model).notice, true);
    assert.equal(model.snapshot().rejection, 'Enter a non-negative whole number.');
    assert.equal(model.snapshot().submission.value.age, 20);
    model.send({ event: { message: { apply: { key: age.key, argument: '21' } } } });
    assert.equal(model.snapshot().rejection, null);
    assert.equal('error' in page(model).notice, false);
  } finally { model.dispose(); }
});

test('order chooses shipping branches, nests visibility, and validates, alongside person in one runtime', async () => {
  const order = await open(fixture('order').start);
  const person = await open(fixture('person').start);
  const control = label => order.snapshot().controls.find(c => c.label === label);
  const apply = (label, argument) => order.send({ event: { message: { apply: { key: control(label).key, argument } } } });
  const submit = () => order.send({ event: { message: 'submit' } });
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
    assert.throws(() => order.send({ apply: { key: control('Shipping').key, argument: 'drone' } }), /Unknown option/);
    apply('Shipping', 'pickup');
    assert.equal(control('Street'), undefined);
    assert.match(outputs(), /Store, Bahnhofstrasse 1/);
    submit();
    assert.equal(JSON.parse(order.snapshot().effects[0].submit.request.body).value.shipping, 'pickup');
    assert.equal(person.snapshot().submission.value.name, 'Ada');
  } finally { order.dispose(); person.dispose(); }
});

test('expenses add, remove, and validate list items', async () => {
  const model = await open(fixture('expenses').start);
  const key = (label, nth = 0) => model.snapshot().controls.filter(c => c.label === label)[nth].key;
  const apply = (label, argument, nth = 0) =>
    model.send({ event: { message: { apply: { key: key(label, nth), argument } } } });
  const submit = () => model.send({ event: { message: 'submit' } });
  const expenses = () => model.snapshot().submission.value.expenses;
  const outputs = () => JSON.stringify(page(model).body);
  try {
    assert.match(outputs(), /CHF 238/);
    apply('Add expense', null);
    assert.deepEqual(expenses().at(-1), { description: '', amount: 0, receipt: false });
    assert.deepEqual(page(model).body[0].group.children[1].group.children.map(c => c.group?.label ?? c.button.label),
      ['Expense 1', 'Expense 2', 'Expense 3', 'Add expense']);
    submit();
    assert.deepEqual(messages(model.snapshot().view), ['Describe the expense.', 'Enter an amount of at least CHF 1.']);
    assert.deepEqual(model.snapshot().errors[0].targets.locations[0],
      [{ kind: 'field', name: 'expenses' }, { kind: 'index', position: 2 }, { kind: 'field', name: 'description' }]);
    apply('Description', 'Taxi', 2);
    apply('Amount (CHF)', '5000', 2);
    // The report limit is checked once every expense is valid.
    assert.deepEqual(messages(model.snapshot().view), ['Attach a receipt for CHF 100 or more.']);
    // Only expenses of CHF 100 or more show a receipt checkbox.
    apply('Receipt attached', true, 1);
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
