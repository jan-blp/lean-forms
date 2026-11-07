import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { openCompiledForm } from './dist/wasm.js';

const cwd = fileURLToPath(new URL('..', import.meta.url));
execFileSync('lake', ['build', 'Forms.Runtime.CompiledForms'], { cwd, stdio: 'pipe' });
const fixtures = JSON.parse(execFileSync('lake', ['env', 'lean', '--run', 'tools/ExportCompiledForms.lean'], {
  cwd, encoding: 'utf8', maxBuffer: 16 * 1024 * 1024,
}));
const fixture = name => fixtures.find(f => f.descriptor.form === name);

function snapshot(model) {
  return { title: model.title, view: model.view(), controls: model.controls(),
    submission: model.submission(), errors: model.errors() };
}
for (const { descriptor, initial, cases } of fixtures) {
  test(`compiled ${descriptor.form} matches native Lean through actions, views, validation, and reset`, async () => {
    const model = await openCompiledForm(descriptor);
    try {
      assert.deepEqual(snapshot(model), initial);
      for (const { action, expected } of cases) {
        model.apply(action.key, action.argument);
        assert.deepEqual(snapshot(model), expected);
        model.reset();
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
    const plus = a.controls().find(c => c.id === 'plusOne').key;
    a.apply(plus); a.apply(plus);
    assert.equal(a.submission().value, '102');
    assert.equal(b.submission().value, '200');
    const copy = a.submission(); copy.actions.length = 0;
    assert.equal(a.submission().actions.length, 2);
    a.reset(); assert.deepEqual(a.submission(), { value: '100', actions: [] });
    a.dispose(); a.dispose();
    assert.throws(() => a.apply(plus), /disposed/);
    b.apply(plus); assert.equal(b.submission().value, '201');
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
    const initial = model.submission();
    const editor = model.controls().find(c => c.kind === 'editor');
    const button = model.controls().find(c => c.kind === 'button');
    for (const raw of ['-1', '', '1.2', false, null]) {
      assert.throws(() => model.apply(editor.key, raw));
      assert.deepEqual(model.submission(), initial);
    }
    assert.throws(() => model.apply(button.key, '1'));
    assert.throws(() => model.apply('missing'));
    assert.deepEqual(model.submission(), initial);
    model.apply(editor.key, ' 003 ');
    assert.deepEqual(model.submission().actions[0].argument, '3');
  } finally { model.dispose(); }
});

test('compiled lists and sums reject stale controls and preserve action ordering', async () => {
  for (const name of ['invoice', 'location', 'person']) {
    const { descriptor } = fixture(name);
    const model = await openCompiledForm(descriptor);
    const act = (control, value) => model.apply(control.key, value);
    try {
      if (name === 'invoice') {
        act(model.controls().find(c => c.id === 'appendDefault'));
        const quantity = model.controls().filter(c => c.label === 'Quantity')[1];
        act(quantity, '7');
        act(model.controls().filter(c => c.id === 'remove')[0]);
        assert.throws(() => model.apply(quantity.key, '9'));
        act(model.controls().find(c => c.label === 'Quantity'), '0');
        assert.ok(model.errors().length);
      } else if (name === 'location') {
        const old = model.controls().find(c => c.kind === 'editor');
        const choice = model.controls().find(c => c.kind === 'choice');
        act(choice, 'Japan');
        assert.throws(() => model.apply(old.key, 0));
        act(choice, 'France');
      } else {
        const checkbox = model.controls().find(c => c.widget === 'checkbox');
        act(checkbox, true);
        const old = model.controls().find(c => c.widget === 'select');
        act(checkbox, false);
        assert.throws(() => model.apply(old.key, 0));
      }
      assert.ok(model.submission().actions.length > 0);
    } finally { model.dispose(); }
  }
});


test('compiled model disposal releases memory and disposed handles stay invalid', async () => {
  const { createFormRuntime } = await import('../experiments/wasm/form-api.mjs');
  const runtime = await createFormRuntime();
  const call = request => runtime.form(JSON.stringify(request));
  const cycle = () => {
    const opened = call({ operation: 'open', ...fixture('counter').descriptor });
    assert.equal(opened.ok, true);
    const { handle, snapshot } = opened.value;
    const key = snapshot.controls.find(c => c.id === 'plusOne').key;
    assert.equal(call({ operation: 'apply', handle, key }).ok, true);
    assert.equal(call({ operation: 'reset', handle }).ok, true);
    assert.equal(call({ operation: 'dispose', handle }).ok, true);
    assert.equal(call({ operation: 'inspect', handle }).ok, false);
    return handle;
  };
  cycle();
  const before = runtime.allocatedBytes();
  for (let i = 0; i < 1000; i++) cycle();
  assert.equal(runtime.allocatedBytes(), before);
  const next = call({ operation: 'open', ...fixture('counter').descriptor });
  const handle = next.value.handle;
  const initial = call({ operation: 'inspect', handle });
  for (const text of ['{', '{}', JSON.stringify({ operation: 'inspect', handle }) + '\0'])
    assert.equal(runtime.form(text).ok, false);
  assert.equal(call({ operation: 'apply', handle, key: 'missing' }).ok, false);
  assert.deepEqual(call({ operation: 'inspect', handle }), initial);
  assert.equal(call({ operation: 'dispose', handle }).ok, true);
});

test('compiled editor normalization preserves whitespace, precision, types, and dates', async () => {
  const counter = await openCompiledForm(fixture('counter').descriptor);
  const person = await openCompiledForm(fixture('person').descriptor);
  const booking = await openCompiledForm(fixture('booking').descriptor);
  try {
    const editor = counter.controls().find(c => c.kind === 'editor');
    for (const code of [9, 10, 11, 12, 13, 32, 160, 0x1680,
      ...Array.from({ length: 11 }, (_, i) => 0x2000 + i), 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff]) {
      const c = String.fromCodePoint(code);
      counter.apply(editor.key, c + '00042' + c);
      assert.equal(counter.submission().value, '42');
      assert.equal(counter.submission().actions.at(-1).argument, '42');
    }
    for (const raw of ['', ' ', '-1', '+1', '1.5', '1e3', '0x10', '1 2', '١', '１',
      '\u00851', '\u180e1', '\u200b1', '1\0', 1, false, null, undefined, {}, []]) {
      const before = counter.submission();
      assert.throws(() => counter.apply(editor.key, raw));
      assert.deepEqual(counter.submission(), before);
    }
    const name = person.controls().find(c => c.widget === 'textInput');
    person.apply(name.key, ' 🌍\0 ');
    assert.equal(person.submission().actions.at(-1).argument, ' 🌍\0 ');
    assert.throws(() => person.apply(name.key, 1));
    const checkbox = person.controls().find(c => c.widget === 'checkbox');
    for (const raw of ['true', 1, 0, null]) assert.throws(() => person.apply(checkbox.key, raw));
    person.apply(checkbox.key, true);
    const select = person.controls().find(c => c.widget === 'select');
    for (const raw of [-1, select.schema.options.length, 0.5, '1', null, Infinity, NaN])
      assert.throws(() => person.apply(select.key, raw));
    person.apply(select.key, 1);
    assert.equal(person.submission().actions.at(-1).argument, 1);
    const date = booking.controls().find(c => c.widget === 'dateInput');
    for (const raw of ['0001-01-01', '9999-12-31', '2000-02-29', '2028-02-29']) {
      booking.apply(date.key, raw);
      assert.equal(booking.submission().actions.at(-1).argument, raw);
    }
    for (const raw of ['0000-01-01', '10000-01-01', '1900-02-29', '2028-02-30',
      '2028-13-01', '2028-01-00', '2028-2-29', ' 2028-02-29', '', null]) {
      const before = booking.submission();
      assert.throws(() => booking.apply(date.key, raw));
      assert.deepEqual(booking.submission(), before);
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
  const result = fresh.form(JSON.stringify({ operation: 'open', ...fixture('counter').descriptor }));
  assert.equal(result.ok, true);
  assert.equal(result.value.snapshot.submission.value, '0');
  assert.equal(fresh.form(JSON.stringify({ operation: 'dispose', handle: result.value.handle })).ok, true);
});
