import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createModel } from './dist/interpreter.js';
import { runChecker, validationErrors } from './dist/validation.js';
import { loadWasmEvaluator } from './dist/wasm.js';

const wasm = await loadWasmEvaluator();
const fixture = name => JSON.parse(readFileSync(new URL(`../Tests/fixtures/${name}.json`, import.meta.url)));
for (const name of ['person', 'counter', 'counters', 'thermostat', 'booking', 'invoice',
  'shapes', 'location', 'report', 'basket', 'weakened-basket', 'weakened-report']) {
  test(`Wasm supports ${name} controls, actions, rendering, errors, and reset`, () => {
    const spec = fixture(name);
    const initial = createModel(spec, wasm);
    for (const control of initial.controls().filter(control => !control.disabled)) {
      const model = createModel(spec, wasm);
      let argument;
      if (control.kind === 'choice') argument = control.options.at(-1);
      else if (control.kind === 'editor') {
        switch (control.schema.kind) {
          case 'natural': argument = (BigInt(control.value) + 123456789012345678901234567890n).toString(); break;
          case 'text': argument = control.value + ' 🌍\0'; break;
          case 'boolean': argument = !control.value; break;
          case 'enum': argument = (control.value + 1) % control.schema.options.length; break;
          default: argument = control.value;
        }
      }
      model.apply(control.key, argument);
      assert.equal(model.submission().actions.length, 1);
      assert.ok(model.view());
      assert.ok(Array.isArray(model.errors()));
      model.reset();
      assert.deepEqual(model.submission(), initial.submission());
      assert.deepEqual(model.view(), initial.view());
      assert.deepEqual(model.errors(), initial.errors());
    }
  });
}

test('Wasm returns result schemas for nested scopes and reports decoding errors', () => {
  assert.deepEqual(wasm({ kind: 'project', path: [] }, [], { kind: 'list', element: { kind: 'natural' } }),
    { value: [], schema: { kind: 'list', element: { kind: 'natural' } } });
  assert.throws(() => wasm({ kind: 'project', path: [] }, '0'), /Missing input schema/);
  assert.throws(() => wasm({ kind: 'natAdd', left: { kind: 'project', path: [] },
    right: { kind: 'value', type: { kind: 'text' }, value: 'x' } }, '0', { kind: 'natural' }), /Type mismatch/);
});

const natural = { kind: 'natural' };
const literal = (type, value) => ({ kind: 'value', type, value });
const report = targets => ({ kind: 'report', message: literal({ kind: 'text' }, 'error'), targets });

test('Wasm checker runs without calling the JavaScript expression evaluator', () => {
  const backend = () => { throw new Error('Unexpected JavaScript expression callback'); };
  backend.runChecker = wasm.runChecker;
  assert.deepEqual(runChecker(report({ kind: 'global' }), natural, '0', backend),
    [{ message: 'error', targets: { kind: 'global' } }]);
});

test('Wasm checker rejects malformed nodes, expressions, and target paths before execution', () => {
  const bad = [
    { kind: 'unknown' }, { kind: 'pass', extra: true },
    { kind: 'seq', left: { kind: 'pass' } },
    { kind: 'ite', condition: literal(natural, '0'), thenBranch: { kind: 'pass' }, elseBranch: { kind: 'pass' } },
    { kind: 'ite', condition: literal({ kind: 'boolean' }, false), thenBranch: { kind: 'pass' }, elseBranch: { kind: 'unknown' } },
    { kind: 'each', items: literal(natural, '0'), body: { kind: 'pass' } },
    { kind: 'each', items: literal({ kind: 'list', element: natural }, []), body: { kind: 'unknown' } },
    { kind: 'report', message: literal(natural, '0'), targets: { kind: 'global' } },
    report({ kind: 'unknown' }), report({ kind: 'locations', locations: [] }),
    report({ kind: 'locations', locations: [[{ kind: 'field', name: 'missing' }]] }),
    report({ kind: 'locations', locations: [[{ kind: 'item', index: literal(natural, '0') }]] }),
    report({ kind: 'locations', locations: [[{ kind: 'constructor', tag: 'missing' }]] }),
  ];
  for (const checker of bad) assert.throws(() => wasm.runChecker(checker, natural, '0'));
  assert.throws(() => wasm.runChecker({ kind: 'pass' }, natural, false));
  assert.throws(() => wasm.runChecker(report({ kind: 'locations', locations: [
    [{ kind: 'item', index: literal({ kind: 'text' }, '0') }],
  ] }), { kind: 'list', element: natural }, []));
  assert.deepEqual(wasm.runChecker({ kind: 'pass' }, natural, '0'), []);
});

test('Wasm checker repeated calls preserve error ordering', () => {
  const checker = { kind: 'seq', left: report({ kind: 'global' }), right: report({ kind: 'locations', locations: [[]] }) };
  const expected = [{ message: 'error', targets: { kind: 'global' } },
    { message: 'error', targets: { kind: 'locations', locations: [[]] } }];
  for (let i = 0; i < 1000; i++) assert.deepEqual(wasm.runChecker(checker, natural, '0'), expected);
});

const base = { kind: 'base' };

test('recursive validation uses one backend call without JavaScript checker callbacks', () => {
  const spec = fixture('invoice');
  const backend = () => { throw new Error('Unexpected expression callback'); };
  backend.runChecker = () => { throw new Error('Unexpected checker callback'); };
  let calls = 0;
  backend.validate = (...args) => { calls++; return wasm.validate(...args); };
  const value = [{ description: 'A', quantity: '0', unitPrice: '0' }];
  assert.deepEqual(validationErrors(spec.validation, spec.schema, value, backend),
    wasm.validate(spec.validation, spec.schema, value));
  assert.equal(calls, 1);
});

test('recursive validation rejects malformed definitions, including unused refinements', () => {
  for (const refinement of [
    { kind: 'unknown' }, { kind: 'base', extra: true },
    { kind: 'refine', inner: base },
    { kind: 'refine', inner: base, checker: { kind: 'unknown' } },
    { kind: 'list', item: base }, { kind: 'record', fields: {} }, { kind: 'sum', branches: {} },
  ]) assert.throws(() => wasm.validate(refinement, natural, '0'));
  assert.throws(() => wasm.validate(base, natural, false));
  assert.throws(() => wasm.validate({ kind: 'list', item: { kind: 'unknown' } },
    { kind: 'list', element: natural }, []));
  const schema = { kind: 'record', fields: [{ name: 'n', type: natural }] };
  for (const fields of [{}, { n: base, extra: base }, { n: { kind: 'unknown' } }])
    assert.throws(() => wasm.validate({ kind: 'record', fields }, schema, { n: '0' }));
  const sum = { kind: 'sum', constructors: [{ name: 'a', type: natural }, { name: 'b', type: natural }] };
  for (const branches of [{ a: base }, { a: base, b: { kind: 'unknown' } }, { a: base, b: base, extra: base }])
    assert.throws(() => wasm.validate({ kind: 'sum', branches }, sum, { tag: 'a', value: '0' }));
  assert.deepEqual(wasm.validate(base, natural, '0'), []);
});


test('input normalization preserves browser whitespace, precision, and scalar types', () => {
  const whitespace = [9, 10, 11, 12, 13, 32, 160, 0x1680,
    ...Array.from({ length: 11 }, (_, i) => 0x2000 + i), 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff];
  for (const code of whitespace) {
    const c = String.fromCodePoint(code);
    assert.equal(wasm.normalize(natural, c + '00042' + c), '42');
  }
  const huge = '123456789012345678901234567890';
  assert.equal(wasm.normalize(natural, '000' + huge), huge);
  for (const input of ['', ' ', '-1', '+1', '1.5', '1e3', '0x10', '1 2', '١', '１',
    '\u00851', '\u180e1', '\u200b1', '1\0', 1, false, null, undefined, {}, []])
    assert.throws(() => wasm.normalize(natural, input));
  const text = { kind: 'text' };
  assert.equal(wasm.normalize(text, ' 🌍\0 '), ' 🌍\0 ');
  assert.equal(wasm.normalize(text, ''), '');
  assert.throws(() => wasm.normalize(text, 1));
  const boolean = { kind: 'boolean' };
  for (const value of [true, false]) assert.equal(wasm.normalize(boolean, value), value);
  for (const value of ['true', 'false', 0, 1, null]) assert.throws(() => wasm.normalize(boolean, value));
});

test('input normalization checks enum bounds and calendar dates', () => {
  const enumeration = { kind: 'enum', options: ['A', 'B'] };
  for (const value of [0, 1]) assert.equal(wasm.normalize(enumeration, value), value);
  for (const value of [-1, 2, 0.5, '1', null, Infinity, NaN])
    assert.throws(() => wasm.normalize(enumeration, value));
  assert.throws(() => wasm.normalize({ kind: 'enum', options: [] }, 0));
  const date = { kind: 'date' };
  for (const value of ['0001-01-01', '9999-12-31', '2000-02-29', '2028-02-29'])
    assert.equal(wasm.normalize(date, value), value);
  for (const value of ['0000-01-01', '10000-01-01', '1900-02-29', '2028-02-30',
    '2028-13-01', '2028-01-00', '2028-2-29', ' 2028-02-29', '', null])
    assert.throws(() => wasm.normalize(date, value));
  for (const [schema, value] of [
    [{ kind: 'list', element: natural }, []],
    [{ kind: 'record', fields: [] }, {}],
    [{ kind: 'sum', constructors: [{ name: 'n', type: natural }] }, { tag: 'n', value: '0' }],
  ]) assert.throws(() => wasm.normalize(schema, value), /Unsupported value type/);
});
