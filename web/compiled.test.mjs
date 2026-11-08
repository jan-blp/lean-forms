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

test('models preserve independent values and reset', async () => {
  const descriptor = fixture('person').descriptor;
  const a = await openCompiledForm({ ...descriptor, value: { ...descriptor.value, age: 25 } });
  const b = await openCompiledForm(descriptor);
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
  const descriptor = fixture('person').descriptor;
  await assert.rejects(openCompiledForm({ ...descriptor, form: 'missing' }), /Unknown compiled form/);
  await assert.rejects(openCompiledForm({ ...descriptor, revision: 'old' }), /version differs/);
  for (const value of [false, {}, { ...descriptor.value, age: '20' }])
    await assert.rejects(openCompiledForm({ ...descriptor, value }));
});

test('hidden and disabled controls reject stale edits', async () => {
  const model = await openCompiledForm(fixture('person').descriptor);
  const apply = (label, argument) => model.send({ apply: {
    key: model.snapshot().controls.find(c => c.label === label).key, argument } });
  try {
    apply('Request delivery', true);
    const key = model.snapshot().controls.find(c => c.label === 'Street').key;
    apply('Age', '17');
    assert.throws(() => model.send({ apply: { key, argument: 'Changed' } }), /unavailable/);
    apply('Age', '20');
    apply('Request delivery', false);
    assert.throws(() => model.send({ apply: { key, argument: 'Changed' } }), /unavailable/);
    assert.equal(model.snapshot().submission.value.address.street, 'Lambda Lane');
  } finally { model.dispose(); }
});

test('compiled model disposal releases memory and disposed handles stay invalid', async () => {
  const { createFormRuntime } = await import('../wasm/form-api.mjs');
  const runtime = await createFormRuntime();
  const call = ({ operation, handle, ...fields }) => runtime.form(JSON.stringify(
    operation === 'open' ? { open: { descriptor: fields } } : operation === 'dispose' ? { dispose: { handle } }
      : { send: { handle, request: Object.keys(fields).length ? { [operation]: fields } : operation } }));
  const cycle = () => {
    const opened = call({ operation: 'open', ...fixture('person').descriptor });
    assert.equal(opened.ok, true);
    const { handle, snapshot } = opened.value.opened;
    const key = snapshot.controls.find(c => c.label === 'Age').key;
    assert.equal(call({ operation: 'apply', handle, key, argument: '21' }).ok, true);
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
  const next = call({ operation: 'open', ...fixture('person').descriptor });
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
  const model = await openCompiledForm(fixture('person').descriptor);
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
  for (const name of ['forms_init', 'forms_request', 'forms_allocated_bytes']) assert.ok(exports.includes(name));
  assert.ok(!exports.some(name => /json_(run|evaluate|check|normalize|validate)/.test(name)));
  const { createFormRuntime } = await import('../wasm/form-api.mjs');
  const trapped = await createFormRuntime();
  assert.throws(() => trapped.form('['.repeat(200000) + ']'.repeat(200000)), /stack overflow|maximum call stack size exceeded/i);
  const fresh = await createFormRuntime();
  const result = fresh.form(JSON.stringify({ open: { descriptor: fixture('person').descriptor } }));
  assert.equal(result.ok, true);
  assert.equal(result.value.opened.snapshot.submission.value.age, 20);
  assert.equal(fresh.form(JSON.stringify({ dispose: { handle: result.value.opened.handle } })).ok, true);
});


test('Lean owns validation visibility, server feedback, and recovery', async () => {
  const model = await openCompiledForm(fixture('person').descriptor);
  const messages = value => {
    if (!value || typeof value !== 'object') return [];
    return [...(value.attributes?.some?.(([name, text]) => name === 'class' && text === 'validation-error') ? [value.text] : []),
      ...Object.values(value).flatMap(messages)];
  };
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

test('Lean owns draft guards, submission effects, pending locks, and reset', async () => {
  const model = await openCompiledForm(fixture('person').descriptor);
  try {
    const editor = model.snapshot().controls.find(c => c.label === 'Age');
    const send = (event, fields = {}) => model.send({ event: { message: event === 'submit' || event === 'reset' ? event : { [event]: fields } } });
    assert.equal(send('draft', { key: editor.key, argument: '07' }).render, false);
    assert.equal(page(model, 'count').text, '0 actions');
    send('submit');
    assert.equal(page(model, 'submit').attributes.some(([name]) => name === 'disabled'), false);
    assert.equal((model.snapshot().effects.length > 0), false);
    assert.equal(page(model, 'status').text, 'Apply your edits before submitting.');
    send('apply', { key: editor.key, argument: '07' });
    assert.equal(model.snapshot().submission.value.age, 7);
    send('submit');
    assert.equal((model.snapshot().effects.length > 0), true);
    const submission = model.snapshot().submission;
    const [effect] = model.snapshot().effects;
    assert.equal(effect.url, '/api/submit');
    assert.equal(effect.method, 'POST');
    assert.equal(effect.headers['Content-Type'], 'application/json');
    assert.deepEqual(JSON.parse(effect.body), submission);
    for (const [event, fields] of [['submit', {}], ['reset', {}], ['apply', { key: editor.key, argument: '8' }],
      ['draft', { key: editor.key, argument: '99' }]]) {
      send(event, fields);
      assert.equal(page(model, 'submit').attributes.some(([name]) => name === 'disabled'), true);
      assert.equal((model.snapshot().effects.length > 0), false);
      assert.deepEqual(model.snapshot().submission, submission);
    }
    assert.throws(() => model.send({ apply: { key: editor.key, argument: '8' } }), /progress/);
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
    assert.equal(JSON.parse(result(model)).age, 7);
    assert.equal(page(model, 'status').attributes.some(([name, value]) => name === 'class' && value === 'error'), false);
    send('complete', { status: 500, body: '' });
    assert.equal(page(model, 'status').text, 'Submitted successfully.');
    send('draft', { key: editor.key, argument: '8' });
    send('draft', { key: editor.key, argument: '7' });
    send('apply', { key: editor.key, argument: '8' });
    assert.equal(result(model), null);
    assert.equal(model.snapshot().submission.value.age, 8);
    send('reset');
    assert.equal(model.snapshot().submission.value.age, 20);
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
    assert.equal(page(b, 'count').text, '0 actions');
    a.send({ event: { message: { failed: { message: 'Offline' } } } });
    a.send({ event: { message: { apply: { key: checkbox.key, argument: true } } } });
    const texts = value => !value || typeof value !== 'object' ? [] :
      [value.value, ...Object.values(value).flatMap(texts)];
    assert.ok(!texts(a.snapshot().view).includes('Hidden draft'));
    assert.throws(() => a.send({ event: { message: { draft: { key: checkbox.key, argument: 'false' } } } }), /drafts/);
  } finally { a.dispose(); b.dispose(); }
});
