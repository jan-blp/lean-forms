import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { openCompiledForm } from './dist/wasm.js';

const cwd = fileURLToPath(new URL('..', import.meta.url));
execFileSync('lake', ['build', 'Forms.Runtime.CompiledRevision'], { cwd, stdio: 'pipe' });
const fixtures = JSON.parse(execFileSync('lake', ['env', 'lean', '--run', 'tools/ExportCompiledForms.lean'], {
  cwd, encoding: 'utf8', maxBuffer: 16 * 1024 * 1024,
}));
const fixture = name => fixtures.find(f => f.descriptor.form === name);

function snapshot(model) { return model.snapshot(); }
function page(model, id) {
  const find = tree => { const node = tree?.element; return node && (node.attributes.some(([name, value]) => name === 'id' && value === id)
    ? node : node.children.map(find).find(Boolean)); };
  return find(model.snapshot().view);
}
function result(model) {
  return page(model, 'result').attributes.some(([name]) => name === 'hidden')
    ? null : page(model, 'result').children.find(node => node?.element.tag === 'pre').element.text;
}
for (const { descriptor, initial, cases } of fixtures) {
  test(`compiled ${descriptor.form} matches native Lean through actions, views, validation, and reset`, async () => {
    const model = await openCompiledForm(descriptor);
    try {
      assert.deepEqual(snapshot(model), initial);
      for (const { action, expected } of cases) {
        model.send({ apply: { key: action.key, argument: action.argument ?? null } });
        assert.deepEqual(snapshot(model), expected);
        model.send('reset');
        assert.deepEqual(snapshot(model), initial);
      }
    } finally { model.dispose(); }
  });
}

test('compiled models preserve arbitrary initial values, independent histories, and reset', async () => {
  const descriptor = fixture('counter').descriptor;
  const a = await openCompiledForm({ ...descriptor, value: '100' });
  const b = await openCompiledForm({ ...descriptor, value: '200' });
  try {
    const plus = a.snapshot().controls.find(c => c.id === 'plusOne').key;
    a.send({ apply: { key: plus, argument: null } }); a.send({ apply: { key: plus, argument: null } });
    assert.equal(a.snapshot().submission.value, '102');
    assert.equal(b.snapshot().submission.value, '200');
    const copy = a.snapshot().submission; copy.actions.length = 0;
    assert.equal(a.snapshot().submission.actions.length, 2);
    a.send('reset'); assert.deepEqual(a.snapshot().submission, { value: '100', actions: [] });
    a.dispose(); a.dispose();
    assert.throws(() => a.send({ apply: { key: plus, argument: null } }), /disposed/);
    b.send({ apply: { key: plus, argument: null } }); assert.equal(b.snapshot().submission.value, '201');
  } finally { a.dispose(); b.dispose(); }
});

test('compiled initialization rejects unknown forms, incompatible revisions, and invalid values', async () => {
  const descriptor = fixture('counter').descriptor;
  await assert.rejects(openCompiledForm({ ...descriptor, form: 'missing' }), /Unknown compiled form/);
  await assert.rejects(openCompiledForm({ ...descriptor, revision: 'old' }), /version differs/);
  await assert.rejects(openCompiledForm({ ...descriptor, value: false }));
});

test('rejected compiled actions leave state and history unchanged', async () => {
  const model = await openCompiledForm(fixture('counter').descriptor);
  try {
    const initial = model.snapshot().submission;
    const editor = model.snapshot().controls.find(c => c.kind === 'editor');
    const button = model.snapshot().controls.find(c => c.kind === 'button');
    for (const raw of ['-1', '', '1.2', false, null]) {
      assert.throws(() => model.send({ apply: { key: editor.key, argument: raw } }));
      assert.deepEqual(model.snapshot().submission, initial);
    }
    assert.throws(() => model.send({ apply: { key: button.key, argument: '1' } }));
    assert.throws(() => model.send({ apply: { key: 'missing', argument: null } }));
    assert.deepEqual(model.snapshot().submission, initial);
    model.send({ apply: { key: editor.key, argument: ' 003 ' } });
    assert.deepEqual(model.snapshot().submission.actions[0].argument, '3');
  } finally { model.dispose(); }
});

test('compiled lists and sums reject stale controls and preserve action ordering', async () => {
  for (const name of ['invoice', 'location', 'person']) {
    const { descriptor } = fixture(name);
    const model = await openCompiledForm(descriptor);
    const act = (control, value = null) => model.send({ apply: { key: control.key, argument: value } });
    try {
      if (name === 'invoice') {
        act(model.snapshot().controls.find(c => c.id === 'appendDefault'));
        const quantity = model.snapshot().controls.filter(c => c.label === 'Quantity')[1];
        act(quantity, '7');
        act(model.snapshot().controls.filter(c => c.id === 'remove')[0]);
        assert.throws(() => model.send({ apply: { key: quantity.key, argument: '9' } }));
        act(model.snapshot().controls.find(c => c.label === 'Quantity'), '0');
        assert.ok(model.snapshot().errors.length);
      } else if (name === 'location') {
        const old = model.snapshot().controls.find(c => c.kind === 'editor');
        const choice = model.snapshot().controls.find(c => c.kind === 'choice');
        act(choice, 'Japan');
        assert.throws(() => model.send({ apply: { key: old.key, argument: 0 } }));
        act(choice, 'France');
      } else {
        const checkbox = model.snapshot().controls.find(c => c.widget === 'checkbox');
        act(checkbox, true);
        const old = model.snapshot().controls.find(c => c.widget === 'select');
        act(checkbox, false);
        assert.throws(() => model.send({ apply: { key: old.key, argument: 0 } }));
      }
      assert.ok(model.snapshot().submission.actions.length > 0);
    } finally { model.dispose(); }
  }
});


test('compiled model disposal releases memory and disposed handles stay invalid', async () => {
  const { createFormRuntime } = await import('../experiments/wasm/form-api.mjs');
  const runtime = await createFormRuntime();
  const call = ({ operation, handle, ...fields }) => runtime.form(JSON.stringify(
    operation === 'open' ? { open: { descriptor: fields } } : operation === 'dispose' ? { dispose: { handle } }
      : { send: { handle, request: Object.keys(fields).length ? { [operation]: fields } : operation } }));
  const cycle = () => {
    const opened = call({ operation: 'open', ...fixture('counter').descriptor });
    assert.equal(opened.ok, true);
    const { handle, snapshot } = opened.value.opened;
    const key = snapshot.controls.find(c => c.id === 'plusOne').key;
    assert.equal(call({ operation: 'apply', handle, key, argument: null }).ok, true);
    assert.equal(call({ operation: 'reset', handle }).ok, true);
    assert.equal(call({ operation: 'dispose', handle }).ok, true);
    assert.equal(call({ operation: 'inspect', handle }).ok, false);
    return handle;
  };
  // Warm the response buffer with four-digit handles before measuring disposal.
  for (let i = 0; i < 1001; i++) cycle();
  const before = runtime.allocatedBytes();
  for (let i = 0; i < 1000; i++) cycle();
  assert.equal(runtime.allocatedBytes(), before);
  const next = call({ operation: 'open', ...fixture('counter').descriptor });
  const handle = next.value.opened.handle;
  const initial = call({ operation: 'inspect', handle });
  for (const text of ['{', '{}', JSON.stringify({ inspect: { handle } }) + '\0'])
    assert.equal(runtime.form(text).ok, false);
  assert.equal(call({ operation: 'apply', handle, key: 'missing', argument: null }).ok, false);
  assert.deepEqual(call({ operation: 'inspect', handle }), initial);
  assert.equal(call({ operation: 'dispose', handle }).ok, true);
});

test('compiled editor normalization preserves whitespace, precision, types, and dates', async () => {
  const counter = await openCompiledForm(fixture('counter').descriptor);
  const person = await openCompiledForm(fixture('person').descriptor);
  const booking = await openCompiledForm(fixture('booking').descriptor);
  try {
    const editor = counter.snapshot().controls.find(c => c.kind === 'editor');
    for (const code of [9, 10, 11, 12, 13, 32, 160, 0x1680,
      ...Array.from({ length: 11 }, (_, i) => 0x2000 + i), 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff]) {
      const c = String.fromCodePoint(code);
      counter.send({ apply: { key: editor.key, argument: c + '00042' + c } });
      assert.equal(counter.snapshot().submission.value, '42');
      assert.equal(counter.snapshot().submission.actions.at(-1).argument, '42');
    }
    for (const raw of ['', ' ', '-1', '+1', '1.5', '1e3', '0x10', '1 2', '1_000', '_1', '1_', '١', '１',
      '\u00851', '\u180e1', '\u200b1', '1\0', 1, false, null, undefined, {}, []]) {
      const before = counter.snapshot().submission;
      assert.throws(() => counter.send({ apply: { key: editor.key, argument: raw } }));
      assert.deepEqual(counter.snapshot().submission, before);
    }
    const name = person.snapshot().controls.find(c => c.widget === 'textInput');
    person.send({ apply: { key: name.key, argument: ' 🌍\0 ' } });
    assert.equal(person.snapshot().submission.actions.at(-1).argument, ' 🌍\0 ');
    assert.throws(() => person.send({ apply: { key: name.key, argument: 1 } }));
    const checkbox = person.snapshot().controls.find(c => c.widget === 'checkbox');
    for (const raw of ['true', 1, 0, null]) assert.throws(() => person.send({ apply: { key: checkbox.key, argument: raw } }));
    person.send({ apply: { key: checkbox.key, argument: true } });
    const select = person.snapshot().controls.find(c => c.widget === 'select');
    for (const raw of [-1, select.options.length, 0.5, '1', null, Infinity, NaN])
      assert.throws(() => person.send({ apply: { key: select.key, argument: raw } }));
    person.send({ apply: { key: select.key, argument: 1 } });
    assert.equal(person.snapshot().submission.actions.at(-1).argument, 1);
    const date = booking.snapshot().controls.find(c => c.widget === 'dateInput');
    for (const raw of ['0001-01-01', '9999-12-31', '2000-02-29', '2028-02-29']) {
      booking.send({ apply: { key: date.key, argument: raw } });
      assert.equal(booking.snapshot().submission.actions.at(-1).argument, raw);
    }
    for (const raw of ['0000-01-01', '10000-01-01', '1900-02-29', '2028-02-30',
      '2028-13-01', '2028-01-00', '2028-2-29', ' 2028-02-29', '', null]) {
      const before = booking.snapshot().submission;
      assert.throws(() => booking.send({ apply: { key: date.key, argument: raw } }));
      assert.deepEqual(booking.snapshot().submission, before);
    }
  } finally { counter.dispose(); person.dispose(); booking.dispose(); }
});

test('Wasm exposes only the compiled-form API and recovers using a fresh instance after a trap', async () => {
  const { readFileSync } = await import('node:fs');
  const binary = readFileSync(new URL('../.lake/wasm/forms.wasm', import.meta.url));
  const exports = WebAssembly.Module.exports(await WebAssembly.compile(binary)).map(e => e.name);
  for (const name of ['forms_init', 'forms_request', 'forms_allocated_bytes']) assert.ok(exports.includes(name));
  assert.ok(!exports.some(name => /json_(run|evaluate|check|normalize|validate)/.test(name)));
  const { createFormRuntime } = await import('../experiments/wasm/form-api.mjs');
  const trapped = await createFormRuntime();
  assert.throws(() => trapped.form('['.repeat(200000) + ']'.repeat(200000)), /stack overflow|maximum call stack size exceeded/i);
  const fresh = await createFormRuntime();
  const result = fresh.form(JSON.stringify({ open: { descriptor: fixture('counter').descriptor } }));
  assert.equal(result.ok, true);
  assert.equal(result.value.opened.snapshot.submission.value, '0');
  assert.equal(fresh.form(JSON.stringify({ dispose: { handle: result.value.opened.handle } })).ok, true);
});


test('Lean owns validation visibility, server feedback, and recovery', async () => {
  const model = await openCompiledForm(fixture('invoice').descriptor);
  const messages = value => {
    if (!value || typeof value !== 'object') return [];
    return [...(value.attributes?.some?.(([name, text]) => name === 'class' && text === 'validation-error') ? [value.text] : []),
      ...Object.values(value).flatMap(messages)];
  };
  try {
    const quantity = model.snapshot().controls.find(c => c.label === 'Quantity');
    model.send({ apply: { key: quantity.key, argument: '0' } });
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
    model.send({ apply: { key: quantity.key, argument: '0' } });
    assert.deepEqual(messages(model.snapshot().view), []);
    model.send('validate');
    assert.equal(model.snapshot().submissionBlocked, true);
  } finally { model.dispose(); }
});

test('Lean owns draft guards, submission effects, pending locks, and reset', async () => {
  const model = await openCompiledForm(fixture('counter').descriptor);
  try {
    const editor = model.snapshot().controls.find(c => c.kind === 'editor');
    const button = model.snapshot().controls.find(c => c.kind === 'button');
    const send = (event, fields = {}) => model.send({ event: { message: event === 'submit' || event === 'reset' ? event : { [event]: fields } } });
    assert.equal(send('draft', { key: editor.key, argument: '07' }).render, false);
    assert.equal(model.snapshot().submission.actions.length, 0);
    send('apply', { key: button.key, argument: null });
    assert.equal(page(model, 'status').text, 'Apply your edits before using this control.');
    assert.equal(model.snapshot().focus, editor.key);
    send('submit');
    assert.equal(page(model, 'submit').attributes.some(([name]) => name === 'disabled'), false);
    assert.equal((model.snapshot().effects.length > 0), false);
    assert.equal(page(model, 'status').text, 'Apply your edits before submitting.');
    send('apply', { key: editor.key, argument: '07' });
    assert.equal(model.snapshot().submission.value, '7');
    send('submit');
    assert.equal((model.snapshot().effects.length > 0), true);
    const submission = model.snapshot().submission;
    const [effect] = model.snapshot().effects;
    assert.equal(effect.url, '/api/submit');
    assert.equal(effect.method, 'POST');
    assert.equal(effect.headers['Content-Type'], 'application/json');
    assert.deepEqual(JSON.parse(effect.body), submission);
    for (const [event, fields] of [['submit', {}], ['reset', {}], ['apply', { key: button.key, argument: null }],
      ['draft', { key: editor.key, argument: '99' }]]) {
      send(event, fields);
      assert.equal(page(model, 'submit').attributes.some(([name]) => name === 'disabled'), true);
      assert.equal((model.snapshot().effects.length > 0), false);
      assert.deepEqual(model.snapshot().submission, submission);
    }
    assert.throws(() => model.send({ apply: { key: button.key, argument: null } }), /progress/);
    assert.throws(() => model.send('reset'), /progress/);
    send('failed', { message: 'Network offline' });
    assert.equal(page(model, 'submit').attributes.some(([name]) => name === 'disabled'), false);
    assert.equal(page(model, 'status').text, 'Network offline');
    send('submit');
    send('complete', { status: 503, body: 'malformed' });
    assert.equal(page(model, 'status').text, 'Submission failed (HTTP 503).');
    assert.equal(page(model, 'submit').attributes.some(([name]) => name === 'disabled'), false);
    send('submit');
    send('complete', { status: 200, body: '' });
    assert.equal(JSON.parse(result(model)), '7');
    assert.equal(page(model, 'status').attributes.some(([name, value]) => name === 'class' && value === 'error'), false);
    send('complete', { status: 500, body: '' });
    assert.equal(page(model, 'status').text, 'Submitted successfully.');
    send('draft', { key: editor.key, argument: '8' });
    send('draft', { key: editor.key, argument: '7' });
    send('apply', { key: button.key, argument: null });
    assert.equal(result(model), null);
    assert.equal(model.snapshot().submission.value, '8');
    send('reset');
    assert.equal(model.snapshot().submission.value, '0');
    assert.equal(page(model, 'count').text, '0 actions');
    send('submit');
    assert.equal((model.snapshot().effects.length > 0), true);
  } finally { model.dispose(); }
});

test('hidden drafts are discarded and UI state stays local to each model', async () => {
  const a = await openCompiledForm(fixture('person').descriptor);
  const b = await openCompiledForm(fixture('person').descriptor);
  try {
    const checkbox = a.snapshot().controls.find(c => c.widget === 'checkbox');
    a.send({ event: { message: { apply: { key: checkbox.key, argument: true } } } });
    const street = a.snapshot().controls.find(c => c.label === 'Street');
    a.send({ event: { message: { draft: { key: street.key, argument: 'Hidden draft' } } } });
    a.send({ event: { message: { apply: { key: checkbox.key, argument: false } } } });
    a.send({ event: { message: 'submit' } });
    assert.equal((a.snapshot().effects.length > 0), true);
    assert.equal(page(b, 'submit').attributes.some(([name]) => name === 'disabled'), false);
    assert.equal(b.snapshot().submission.actions.length, 0);
    a.send({ event: { message: { failed: { message: 'Offline' } } } });
    a.send({ event: { message: { apply: { key: checkbox.key, argument: true } } } });
    const texts = value => !value || typeof value !== 'object' ? [] :
      [value.value, ...Object.values(value).flatMap(texts)];
    assert.ok(!texts(a.snapshot().view).includes('Hidden draft'));
    assert.throws(() => a.send({ event: { message: { draft: { key: checkbox.key, argument: 'false' } } } }), /drafts/);
  } finally { a.dispose(); b.dispose(); }
});
