import test from 'node:test';
import assert from 'node:assert/strict';
import { sameLocation } from './dist/validation.js';

test('error locations distinguish fields, indices, and constructor tags', () => {
  assert.equal(sameLocation([{ kind: 'constructor', tag: 'value' }], [{ kind: 'field', name: 'value' }]), false);
  assert.equal(sameLocation([{ kind: 'item', index: '0' }], [{ kind: 'field', name: '0' }]), false);
  assert.equal(sameLocation([{ kind: 'constructor', tag: 'circle' }], [{ kind: 'constructor', tag: 'rectangle' }]), false);
  assert.equal(sameLocation([{ index: '0', kind: 'item' }], [{ kind: 'item', index: '0' }]), true);
});
