import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createModel } from './dist/interpreter.js';
import { runChecker } from './dist/validation.js';
import { loadWasmEvaluator } from './dist/wasm.js';

const wasm = await loadWasmEvaluator();
const fixture = name => JSON.parse(readFileSync(new URL(`../Tests/fixtures/${name}.json`, import.meta.url)));
function compare(native, compiled) {
  assert.deepEqual(compiled.view(), native.view());
  assert.deepEqual(compiled.controls(), native.controls());
  assert.deepEqual(compiled.submission(), native.submission());
  assert.deepEqual(compiled.errors(), native.errors());
}

for (const name of ['person', 'counter', 'counters', 'thermostat', 'booking', 'invoice',
  'shapes', 'location', 'report', 'basket', 'weakened-basket', 'weakened-report']) {
  test(`Wasm matches TypeScript for ${name} controls, actions, rendering, and errors`, () => {
    const spec = fixture(name);
    compare(createModel(spec), createModel(spec, wasm));
    for (const control of createModel(spec).controls().filter(control => !control.disabled)) {
      const native = createModel(spec);
      const compiled = createModel(spec, wasm);
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
      native.apply(control.key, argument);
      compiled.apply(control.key, argument);
      compare(native, compiled);
      native.reset(); compiled.reset();
      compare(native, compiled);
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
    { kind: 'when', condition: literal(natural, '0'), body: { kind: 'pass' } },
    { kind: 'when', condition: literal({ kind: 'boolean' }, false), body: { kind: 'unknown' } },
    { kind: 'each', items: literal(natural, '0'), body: { kind: 'pass' } },
    { kind: 'each', items: literal({ kind: 'list', element: natural }, []), body: { kind: 'unknown' } },
    { kind: 'report', message: literal(natural, '0'), targets: { kind: 'global' } },
    report({ kind: 'unknown' }), report({ kind: 'fields', locations: [] }),
    report({ kind: 'fields', locations: [[{ kind: 'field', name: 'missing' }]] }),
    report({ kind: 'fields', locations: [[{ kind: 'item', index: literal(natural, '0') }]] }),
    report({ kind: 'fields', locations: [[{ kind: 'constructor', tag: 'missing' }]] }),
  ];
  for (const checker of bad) assert.throws(() => wasm.runChecker(checker, natural, '0'));
  assert.throws(() => wasm.runChecker({ kind: 'pass' }, natural, false));
  assert.throws(() => wasm.runChecker(report({ kind: 'fields', locations: [
    [{ kind: 'item', index: literal({ kind: 'text' }, '0') }],
  ] }), { kind: 'list', element: natural }, []));
  assert.deepEqual(wasm.runChecker({ kind: 'pass' }, natural, '0'), []);
});

test('Wasm checker repeated calls preserve error ordering', () => {
  const checker = { kind: 'seq', left: report({ kind: 'global' }), right: report({ kind: 'fields', locations: [[]] }) };
  const expected = [{ message: 'error', targets: { kind: 'global' } },
    { message: 'error', targets: { kind: 'fields', locations: [[]] } }];
  for (let i = 0; i < 1000; i++) assert.deepEqual(wasm.runChecker(checker, natural, '0'), expected);
});
