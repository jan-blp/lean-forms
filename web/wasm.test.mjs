import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createModel } from './dist/interpreter.js';
import { runChecker } from './dist/validation.js';
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
