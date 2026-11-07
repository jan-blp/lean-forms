import test from 'node:test';
import assert from 'node:assert/strict';
import { formatValue } from './dist/display.js';
import { sameLocation } from './dist/validation.js';

test('display formatting preserves nested values and treats text as text', () => {
  assert.equal(formatValue({ kind: 'text' }, '<img src=x>'), '<img src=x>');
  assert.equal(formatValue({ kind: 'list', element: { kind: 'boolean' } }, [true, false]), '[true, false]');
  const schema = { kind: 'record', fields: [{ name: 'day', type: { kind: 'date' } }] };
  assert.equal(formatValue(schema, { day: '2028-02-29' }), '{day: 2028-02-29}');
  assert.equal(formatValue({ kind: 'sum', constructors: [{ name: 'day', type: { kind: 'date' } }] },
    { tag: 'day', value: '2028-02-29' }), 'day: 2028-02-29');
  assert.equal(formatValue({ kind: 'enum', options: ['A', 'B'] }, 1), 'B');
});

test('error locations distinguish fields, indices, and constructor tags', () => {
  assert.equal(sameLocation([{ kind: 'constructor', tag: 'value' }], [{ kind: 'field', name: 'value' }]), false);
  assert.equal(sameLocation([{ kind: 'item', index: '0' }], [{ kind: 'field', name: '0' }]), false);
  assert.equal(sameLocation([{ kind: 'constructor', tag: 'circle' }], [{ kind: 'constructor', tag: 'rectangle' }]), false);
  assert.equal(sameLocation([{ index: '0', kind: 'item' }], [{ kind: 'item', index: '0' }]), true);
});
