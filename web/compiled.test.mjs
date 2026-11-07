import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { createModel } from './dist/interpreter.js';
import { loadWasmEvaluator, openCompiledForm } from './dist/wasm.js';

const cwd = fileURLToPath(new URL('..', import.meta.url));
execFileSync('lake', ['build', 'Forms.Runtime.CompiledForms'], { cwd, stdio: 'pipe' });
const fixtures = JSON.parse(execFileSync('lake', ['env', 'lean', '--run', 'tools/ExportCompiledForms.lean'], {
  cwd, encoding: 'utf8', maxBuffer: 16 * 1024 * 1024,
}));
const wasm = await loadWasmEvaluator();
const fixture = name => fixtures.find(f => f.descriptor.form === name);

// Compare only display data: compiled controls deliberately contain no programs or defaults.
function display(node) {
  if (!node) return null;
  if (['button', 'editor', 'choice'].includes(node.kind)) {
    const { key, id, target, label, kind, disabled } = node;
    const common = { key, id, target, label, kind, disabled };
    if (kind === 'button') return { ...common, keepDrafts: node.keepDrafts ?? node.effect.kind === 'appendDefault' };
    const { location, value } = node;
    if (kind === 'choice') return { ...common, location, value, options: node.options };
    return { ...common, location, value, schema: node.schema, widget: node.widget };
  }
  const result = structuredClone(node);
  if ('children' in node) result.children = node.children.map(display);
  if (node.kind === 'list') {
    result.append = display(node.append);
    result.items = node.items.map(item => ({ body: display(item.body), remove: display(item.remove) }));
  }
  if (node.kind === 'sum') { result.selector = display(node.selector); result.body = display(node.body); }
  return result;
}
function compare(legacy, compiled) {
  assert.deepEqual(compiled.view(), display(legacy.view()));
  assert.deepEqual(compiled.controls(), legacy.controls().map(display));
  assert.deepEqual(compiled.submission(), legacy.submission());
  assert.deepEqual(compiled.errors(), legacy.errors());
}
function argument(control) {
  if (control.kind === 'choice') return control.options.at(-1);
  if (control.kind !== 'editor') return undefined;
  switch (control.schema.kind) {
    case 'natural': return '00' + (BigInt(control.value) + 123456789012345678901234567890n);
    case 'text': return control.value + ' 🌍\0';
    case 'boolean': return !control.value;
    case 'enum': return (control.value + 1) % control.schema.options.length;
    default: return control.value;
  }
}
for (const { descriptor, specification } of fixtures) {
  test(`compiled ${descriptor.form} matches JSON model through actions, views, validation, and reset`, async () => {
    const compiled = await openCompiledForm(descriptor);
    try {
      const legacy = createModel(specification, wasm);
      compare(legacy, compiled);
      for (const control of legacy.controls().filter(c => !c.disabled)) {
        const raw = argument(control);
        compiled.apply(control.key, raw);
        legacy.apply(control.key, raw);
        compare(legacy, compiled);
        compiled.reset(); legacy.reset();
        compare(legacy, compiled);
      }
    } finally { compiled.dispose(); }
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
    const { descriptor, specification } = fixture(name);
    const model = await openCompiledForm(descriptor);
    const legacy = createModel(specification, wasm);
    const act = (control, value) => { model.apply(control.key, value); legacy.apply(control.key, value); compare(legacy, model); };
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
      compare(legacy, model);
    } finally { model.dispose(); }
  }
});


test('compiled model disposal releases memory and disposed handles stay invalid', async () => {
  const { createEvaluator } = await import('../experiments/wasm/json-api.mjs');
  const runtime = await createEvaluator();
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
  for (let i = 0; i < 100; i++) cycle();
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
