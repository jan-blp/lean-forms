import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { runChecker, validationErrors } from './dist/validation.js';

const cwd = fileURLToPath(new URL('..', import.meta.url));
execFileSync('lake', ['build', 'Tests.ValidationCheckers', 'Forms.Runtime.JsonProtocol'], { cwd, stdio: 'pipe' });
const fixtures = JSON.parse(execFileSync('lake', ['env', 'lean', '--run', 'tools/ExportValidation.lean'], {
  cwd, encoding: 'utf8', maxBuffer: 16 * 1024 * 1024,
}));

for (const fixture of fixtures) {
  test(`serialized validation matches Lean: ${fixture.name}`, () => {
    const original = structuredClone(fixture);
    for (const sample of fixture.samples) {
      const errors = fixture.specification.validation
        ? validationErrors(fixture.specification.validation, fixture.specification.schema, sample.value)
        : runChecker(fixture.specification.checker, fixture.specification.schema, sample.value);
      assert.deepEqual(errors, sample.errors);
      if ('accepted' in sample) assert.equal(errors.length === 0, sample.accepted);
    }
    assert.deepEqual(fixture, original);
  });
}

test('validation rejects malformed checker operations', () => {
  const specification = fixtures.find(fixture => fixture.name === 'invoice').specification;
  assert.throws(() => runChecker({ kind: 'unknown' }, specification.schema, []), /Unsupported/);
  assert.throws(() => runChecker({
    kind: 'when', condition: { kind: 'value', value: 'true' }, body: { kind: 'pass' },
  }, specification.schema, []), /boolean/);
  assert.throws(() => runChecker({
    kind: 'each', items: { kind: 'value', value: 'not a list' }, body: { kind: 'pass' },
  }, specification.schema, []), /list/);
  assert.throws(() => runChecker({
    kind: 'report', message: { kind: 'value', value: 'Empty targets' }, targets: { kind: 'fields', locations: [] },
  }, specification.schema, []), /nonempty/);
});

test('locations distinguish fields, indices, and constructor tags', async () => {
  const { sameLocation } = await import('./dist/validation.js');
  assert.equal(sameLocation([{ kind: 'constructor', tag: 'value' }], [{ kind: 'field', name: 'value' }]), false);
  assert.equal(sameLocation([{ kind: 'item', index: '0' }], [{ kind: 'field', name: '0' }]), false);
  assert.equal(sameLocation([{ kind: 'constructor', tag: 'circle' }], [{ kind: 'constructor', tag: 'rectangle' }]), false);
  assert.equal(sameLocation([{ index: '0', kind: 'item' }], [{ kind: 'item', index: '0' }]), true);
});
