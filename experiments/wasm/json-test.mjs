import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createEvaluator } from './json-api.mjs';

const cases = readFileSync(new URL('../../.lake/wasm/json-cases.jsonl', import.meta.url), 'utf8')
  .trim().split('\n').map(line => JSON.parse(line));
assert.ok(cases.length > 100, 'Expected the full native round-trip/rejection corpus');
const evaluator = await createEvaluator();
const requests = cases.map(test => ({ ...test,
  args: [test.schema, test.expression, test.argument].map(value => JSON.stringify(value)),
}));
const runCases = () => {
  for (const { name, args, expected } of requests) {
    assert.deepEqual(evaluator.evaluate(...args), expected, name);
  }
};
runCases();

const schema = '{"kind":"natural"}';
const expression = '{"kind":"project","path":[]}';
const argument = '"42"';
for (const [args, prefix] of [
  [['{', expression, argument], 'schema:'],
  [[schema, '{', argument], 'expression:'],
  [[schema, expression, '{'], 'value:'],
  [[schema, expression, argument + '\0'], 'value:'],
]) {
  const result = evaluator.evaluate(...args);
  assert.equal(result.ok, false);
  assert.ok(result.error.startsWith(prefix), result.error);
}
// A malformed request must not poison subsequent requests.
assert.deepEqual(evaluator.evaluate(schema, expression, argument), { ok: true, value: '42' });
assert.throws(() => evaluator.evaluate({}, expression, argument), TypeError);

// Warm all lazy constants and allocation caches before measuring retained memory.
runCases();
const before = evaluator.allocatedBytes();
const started = performance.now();
for (let round = 0; round < 100; round++) runCases();
const elapsed = performance.now() - started;
const after = evaluator.allocatedBytes();
assert.equal(after, before, 'Repeated JSON evaluations must not retain additional live allocations');

// Each module instance must initialize its own constants correctly.
const independent = await createEvaluator();
for (const { name, args, expected } of requests) {
  assert.deepEqual(independent.evaluate(...args), expected, `independent instance: ${name}`);
}
// Deep nesting must trap on stack overflow rather than corrupt static data.
const deep = await createEvaluator();
const depth = 200000;
assert.throws(() => deep.evaluate(schema, expression, '['.repeat(depth) + ']'.repeat(depth)),
  /stack overflow|maximum call stack size exceeded/i);
const fresh = await createEvaluator();
assert.deepEqual(fresh.evaluate(schema, expression, argument), { ok: true, value: '42' });
const rejected = cases.filter(test => !test.expected.ok).length;
console.log(`PASS: ${cases.length - rejected} round trips and ${rejected} rejections match native Lean`);
console.log('PASS: malformed JSON, embedded NUL, recovery, and independent module initialization');
console.log(`PASS: ${depth}-deep nesting traps on stack overflow; a fresh instance still works`);
console.log(`PASS: ${cases.length * 100} repeated calls; live allocation bytes ${before} → ${after}`);
console.log(`Repeated test batches: ${elapsed.toFixed(0)} ms (includes JS assertions; not a standalone benchmark)`);

const pass = '{"kind":"pass"}';
assert.deepEqual(evaluator.check(schema, pass, argument), { ok: true, value: [] });
for (const [args, prefix] of [
  [['{', pass, argument], 'schema:'],
  [[schema, '{', argument], 'checker:'],
  [[schema, pass + '\0', argument], 'checker:'],
  [[schema, pass, '{'], 'value:'],
]) {
  const result = evaluator.check(...args);
  assert.equal(result.ok, false);
  assert.ok(result.error.startsWith(prefix), result.error);
}
const checker = JSON.stringify({ kind: 'each', items: { kind: 'project', path: [] }, body: {
  kind: 'report', message: { kind: 'value', type: { kind: 'text' }, value: 'hello 🌍\0' },
  targets: { kind: 'fields', locations: [[{ kind: 'item', index: { kind: 'project', path: ['index'] } }]] },
} });
const listSchema = '{"kind":"list","element":{"kind":"natural"}}';
const listValue = '["1","2"]';
const expectedErrors = { ok: true, value: ['0', '1'].map(index => ({ message: 'hello 🌍\0',
  targets: { kind: 'fields', locations: [[{ kind: 'item', index }]] } })) };
assert.deepEqual(evaluator.check(listSchema, checker, listValue), expectedErrors);
const checkerBefore = evaluator.allocatedBytes();
for (let i = 0; i < 1000; i++) assert.deepEqual(evaluator.check(listSchema, checker, listValue), expectedErrors);
assert.equal(evaluator.allocatedBytes(), checkerBefore);
assert.deepEqual(independent.check(listSchema, checker, listValue), expectedErrors);
console.log('PASS: checker transport, nested scope, Unicode/NUL, recovery, independent initialization, and 1000 calls without retained allocations');
