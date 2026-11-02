import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createModel, evaluate, formatValue } from './dist/interpreter.js';

const fixture = name => JSON.parse(readFileSync(new URL(`../native/tui/tests/${name}.json`, import.meta.url)));
const press = (model, id, target = []) => model.apply(model.controls().find(c => c.id === id && JSON.stringify(c.target) === JSON.stringify(target)).key);

test('actions preserve order, repetitions, and arbitrary precision', () => {
  const model = createModel(fixture('counter'));
  const huge = '123456789012345678901234567890';
  model.apply(model.controls().find(c => c.kind === 'editor').key, huge);
  press(model, 'plusOne');
  press(model, 'plusOne');
  press(model, 'minusOne');
  assert.deepEqual(model.submission(), { value: (BigInt(huge) + 1n).toString(), actions: [
    { target: [], action: 'replace', argument: huge },
    { target: [], action: 'plusOne' }, { target: [], action: 'plusOne' }, { target: [], action: 'minusOne' },
  ] });
  model.reset();
  press(model, 'minusOne');
  assert.equal(model.submission().value, '0');
  assert.equal(model.submission().actions.length, 1);
});

test('invalid arguments leave value and history intact', () => {
  const model = createModel(fixture('counter'));
  const editor = model.controls().find(c => c.kind === 'editor');
  for (const argument of ['-1', '1.5', '', '1e3']) assert.throws(() => model.apply(editor.key, argument));
  assert.throws(() => model.apply(model.controls()[0].key, '5'));
  assert.deepEqual(model.submission(), { value: '0', actions: [] });
});

test('stack targets survive display reordering and shared submission objects cannot mutate state', () => {
  const spec = fixture('counters');
  spec.form.children.reverse();
  spec.form.childIds.reverse();
  const model = createModel(spec);
  press(model, 'plusFive', ['right']);
  press(model, 'plusOne', ['left']);
  const result = model.submission();
  assert.deepEqual(result.value, { left: '1', right: '15' });
  assert.deepEqual(result.actions.map(a => a.target), [['right'], ['left']]);
  result.value.left = '999';
  result.actions.length = 0;
  assert.equal(model.submission().value.left, '1');
  assert.equal(model.submission().actions.length, 2);
});

test('conditions are checked against the current value', () => {
  for (const kind of ['visibleWhen', 'disabledWhen']) {
    const spec = fixture('counter');
    const zero = { kind: 'natLe', left: { kind: 'project', path: [] }, right: { kind: 'value', value: '0' } };
    spec.form = { kind, condition: kind === 'visibleWhen' ? zero : { kind: 'not', operand: zero }, body: spec.form };
    const model = createModel(spec);
    const key = model.controls()[0].key;
    model.apply(key);
    assert.throws(() => model.apply(key));
    assert.equal(model.submission().value, '1');
  }
});

test('editor expressions receive both current value and normalized argument', () => {
  const spec = fixture('counter');
  const editor = spec.form.actions.find(c => c.kind === 'editor');
  editor.body = { kind: 'natAdd', left: { kind: 'project', path: ['current'] }, right: { kind: 'project', path: ['argument'] } };
  const model = createModel(spec);
  press(model, 'plusFive');
  model.apply(model.controls().find(c => c.kind === 'editor').key, '003');
  assert.equal(model.submission().value, '8');
  assert.equal(model.submission().actions.at(-1).argument, '3');
});

test('person fields preserve groups, typed arguments, and visibility', () => {
  const model = createModel(fixture('person'));
  assert.equal(model.view().label, 'Registration');
  assert.equal(model.view().children.length, 3);
  const edit = (widget, argument) => model.apply(model.controls().find(c => c.widget === widget).key, argument);
  edit('textInput', 'Grace');
  edit('checkbox', true);
  const address = model.view().children.at(-1);
  assert.equal(address.label, 'Address');
  edit('select', 2);
  assert.equal(model.submission().value.name, 'Grace');
  assert.equal(model.submission().value.address.kind, 2);
  assert.deepEqual(model.submission().actions.at(-1), { target: ['address', 'kind'], action: 'replace', argument: 2 });
  const stale = model.controls().find(c => c.widget === 'select').key;
  edit('checkbox', false);
  assert.throws(() => model.apply(stale, 0));
  assert.equal(model.submission().value.address.kind, 2);
  const copy = model.view();
  copy.children.length = 0;
  assert.equal(model.view().children.length, 3);
});

test('dates reject invalid calendar dates without recording actions', () => {
  const model = createModel(fixture('booking'));
  const key = model.controls()[0].key;
  for (const value of ['', '2028-02-30', '2027-02-29', '0000-01-01', '2028-13-01', '28-01-01']) {
    assert.throws(() => model.apply(key, value));
  }
  assert.equal(model.submission().actions.length, 0);
  model.apply(key, '2028-02-29');
  assert.equal(model.submission().value.startDate, '2028-02-29');
});

test('standalone buttons evaluate in the enclosing state', () => {
  const spec = fixture('person');
  spec.form = { kind: 'button', label: 'Rename', action: {
    kind: 'set', path: ['name'], value: { kind: 'project', path: ['address', 'street'] },
  } };
  const model = createModel(spec);
  press(model, 'press');
  assert.equal(model.submission().value.name, spec.value.address.street);
  assert.deepEqual(model.submission().actions, [{ target: [], action: 'press' }]);
});

test('action widgets support non-numeric values', () => {
  const model = createModel({ version: 8, value: false, form: {
    kind: 'actionWidget', path: [], label: 'Enabled', schema: { kind: 'boolean' }, actions: [
      { id: 'toggle', label: 'Toggle', kind: 'button', body: { kind: 'not', operand: { kind: 'project', path: [] } } },
      { id: 'replace', label: 'Enabled', kind: 'editor', widget: 'checkbox', body: { kind: 'project', path: ['argument'] } },
    ],
  } });
  press(model, 'toggle');
  assert.equal(model.submission().value, true);
  model.apply(model.controls()[1].key, false);
  assert.equal(model.submission().value, false);
  assert.throws(() => model.apply(model.controls()[1].key, 'false'));
});

const constant = value => ({ kind: 'value', value });
const project = (...path) => ({ kind: 'project', path });

test('computed invoice subtotal updates without adding derived state or actions', () => {
  const spec = fixture('invoice');
  const item = spec.form.children.find(child => child.kind === 'list').item;
  const model = createModel({ version: 8, value: spec.value[0], form: item });
  const subtotal = () => model.view().children.find(child => child.kind === 'computed').value;
  assert.equal(subtotal(), '100');
  const quantity = model.controls().find(control => control.path[0] === 'quantity');
  const huge = '123456789012345678901234567890';
  model.apply(quantity.key, huge);
  assert.equal(subtotal(), (BigInt(huge) * 100n).toString());
  assert.equal(model.controls().length, 3);
  assert.deepEqual(model.submission().value, { ...spec.value[0], quantity: huge });
  assert.deepEqual(model.submission().actions, [{ target: quantity.target, action: 'replace', argument: huge }]);
  assert.throws(() => model.apply(JSON.stringify([['extra'], 'replace']), '5'));
  model.reset();
  assert.equal(subtotal(), '100');
});

test('text and computed displays respect visibility, update, and cannot be invoked', () => {
  const spec = fixture('counter');
  const summary = { kind: 'text', expression: { kind: 'textAppend', left: constant('Count: '),
    right: { kind: 'natToText', operand: project() } } };
  spec.form = { kind: 'stack', childIds: ['edit', 'summary'], children: [spec.form,
    { kind: 'visibleWhen', condition: { kind: 'natLe', left: constant('1'), right: project() },
      body: { kind: 'disabledWhen', condition: constant(true), body: summary } }] };
  const model = createModel(spec);
  assert.equal(model.view().children.length, 1);
  press(model, 'plusOne', ['edit']);
  assert.equal(model.view().children[1].value, 'Count: 1');
  assert.equal(model.controls().length, 4);
  assert.throws(() => model.apply(undefined));
  assert.equal(model.submission().actions.length, 1);
  const onlyText = createModel({ version: 8, value: '2', form: summary });
  assert.deepEqual(onlyText.controls(), []);
  assert.equal(onlyText.view().value, 'Count: 2');
});

test('summary expressions preserve context and natural precision', () => {
  const spec = fixture('invoice');
  const total = spec.form.children.find(child => child.kind === 'computed').expression;
  assert.equal(evaluate(total, []), '0');
  assert.equal(evaluate(total, [{ quantity: '9007199254740993', unitPrice: '2' }, { quantity: '3', unitPrice: '5' }]), '18014398509482001');
  assert.equal(evaluate({ kind: 'length', items: project() }, ['a', 'b']), '2');
  assert.equal(evaluate({ kind: 'enumLabel', subject: constant(1), options: ['Home', 'Work'] }, {}), 'Work');
  assert.equal(evaluate({ kind: 'enumCases', subject: project('choice'), branches: [constant('unused'), project('name')] }, { choice: 1, name: 'Ada' }), 'Ada');
  assert.equal(evaluate({ kind: 'enumEq', left: constant(0), right: constant(1) }, {}), false);
  for (const [left, right, expected] of [['2028-02-29', '2028-03-01', true], ['2028-03-01', '2028-03-01', true], ['2028-03-01', '2028-02-29', false]]) {
    assert.equal(evaluate({ kind: 'dateLe', left: constant(left), right: constant(right) }, {}), expected);
  }
});

test('computed values format recursively using their schema', () => {
  const person = fixture('person');
  assert.equal(formatValue(person.schema, person.value), '{name: Ada, age: 28, subscribed: false, address: {street: Lambda Lane, kind: Home}}');
  assert.equal(formatValue({ kind: 'list', element: { kind: 'boolean' } }, [true, false]), '[true, false]');
  assert.equal(formatValue({ kind: 'sum', constructors: [{ name: 'date', type: { kind: 'date' } }] }, { tag: 'date', value: '2028-02-29' }), 'date: 2028-02-29');
  assert.equal(formatValue({ kind: 'text' }, '<img src=x>'), '<img src=x>');
});

test('all component fixtures render including weakened queries', () => {
  for (const name of ['counter', 'counters', 'person', 'booking', 'invoice', 'location', 'shapes', 'basket', 'report', 'thermostat', 'weakened-basket', 'weakened-report']) {
    const model = createModel(fixture(name));
    assert.ok(model.view(), name);
    assert.deepEqual(model.submission().actions, [], name);
  }
});

test('list actions use current indices and isolate default items', () => {
  const model = createModel(fixture('invoice'));
  press(model, 'appendDefault', ['body']);
  const quantity = model.controls().find(c => c.label === 'Quantity' && c.target[1] === 1);
  model.apply(quantity.key, '7');
  assert.equal(model.submission().value[0].quantity, '1');
  assert.equal(model.submission().value[1].quantity, '7');
  const remove = model.controls().find(c => c.id === 'remove' && c.effect.index === 0);
  model.apply(remove.key);
  assert.equal(model.submission().value[0].quantity, '7');
  assert.deepEqual(model.submission().actions.at(-1), { target: ['body'], action: 'remove', index: 0 });
  assert.throws(() => model.apply(quantity.key, '9'));
  model.apply(model.controls().find(c => c.label === 'Quantity').key, '8');
  press(model, 'appendDefault', ['body']);
  assert.equal(model.submission().value[1].quantity, '1');
  assert.equal(model.view().children[1].value, '900');
  while (model.submission().value.length) model.apply(model.controls().find(c => c.id === 'remove').key);
  assert.equal(model.view().children[1].value, '0');
});

test('sum selection resets payload only when changing constructor', () => {
  const model = createModel(fixture('location'));
  const choose = tag => model.apply(model.controls().find(c => c.kind === 'choice').key, tag);
  const city = model.controls().find(c => c.kind === 'editor');
  model.apply(city.key, 1);
  choose('France');
  assert.equal(model.submission().value.value, 1);
  choose('Japan');
  assert.throws(() => model.apply(city.key, 0));
  assert.deepEqual(model.submission().value, { tag: 'Japan', value: 0 });
  assert.deepEqual(model.submission().actions.at(-1), { target: [], action: 'select', constructor: 'Japan' });
  choose('France');
  assert.equal(model.submission().value.value, 0);
  assert.throws(() => choose('unknown'));
});

test('nested lists and sums evaluate guards and actions in local state', () => {
  const field = { kind: 'field', path: [], label: 'Value', widget: 'naturalInput', schema: { kind: 'natural' } };
  const choice = { kind: 'sum', path: [], label: 'Choice', schema: { kind: 'sum', constructors: [{ name: 'number', type: { kind: 'natural' } }] },
    defaults: { number: '1' }, branches: { number: { kind: 'disabledWhen', condition: { kind: 'natLe', left: constant('5'), right: project() }, body: field } } };
  const model = createModel({ version: 8, value: [[{ tag: 'number', value: '1' }]], form: {
    kind: 'list', path: [], label: 'Outer', defaultItem: [], item: {
      kind: 'list', path: [], label: 'Inner', defaultItem: { tag: 'number', value: '1' }, item: choice,
    },
  } });
  const editor = model.controls().find(c => c.kind === 'editor');
  model.apply(editor.key, '5');
  assert.deepEqual(model.submission().actions[0], { target: [0, 0, 'number'], action: 'replace', argument: '5' });
  assert.equal(model.submission().value[0][0].value, '5');
  assert.throws(() => model.apply(editor.key, '2'));
});

test('tables update from filtered and sorted rows without reordering stored data', () => {
  const rows = [{ name: 'B', n: '2' }, { name: 'A', n: '1' }, { name: 'C', n: '2' }];
  const sort = { kind: 'sortNatBy', items: project(), key: project('n'), descending: true };
  const model = createModel({ version: 8, value: rows, form: { kind: 'table', rows: sort,
    columns: [{ label: 'Name', expression: project('name') }] } });
  assert.deepEqual(model.view().rows, [['B'], ['C'], ['A']]);
  assert.deepEqual(model.submission().value, rows);
  assert.deepEqual(model.controls(), []);
  assert.deepEqual(evaluate({ kind: 'filter', items: project(), predicate: { kind: 'natLe', left: project('n'), right: constant('1') } }, rows), [rows[1]]);
  assert.equal(evaluate({ kind: 'all', items: constant([]), predicate: constant(false) }, rows), true);
});

test('query ordering and search match Lean Unicode and ASCII semantics', () => {
  assert.deepEqual(evaluate({ kind: 'sortBy', items: project(), key: project(), descending: false }, ['\u{10000}', '\ue000', 'a']), ['a', '\ue000', '\u{10000}']);
  const search = query => evaluate({ kind: 'search', items: project(), key: project(), query: constant(query) }, ['Alpha', 'ALP', 'Ä', 'ä']);
  assert.deepEqual(search('alp'), ['Alpha', 'ALP']);
  assert.deepEqual(search('ä'), ['ä']);
  assert.equal(evaluate({ kind: 'cases', subject: project(), branches: { number: { kind: 'natAdd', left: project(), right: constant('2') } } }, { tag: 'number', value: '3' }), '5');
  const values = ['1'];
  assert.deepEqual(evaluate({ kind: 'snoc', items: project(), value: constant('2') }, values), ['1', '2']);
  assert.deepEqual(values, ['1']);
});

test('hidden and disabled containers prevent structural actions', () => {
  for (const name of ['invoice', 'location']) {
    for (const kind of ['visibleWhen', 'disabledWhen']) {
      const spec = fixture(name);
      spec.form = { kind, condition: constant(kind === 'disabledWhen'), body: spec.form };
      const model = createModel(spec);
      if (kind === 'visibleWhen') assert.deepEqual(model.controls(), []);
      else for (const control of model.controls()) {
        assert.equal(control.disabled, true);
        assert.throws(() => model.apply(control.key));
      }
      assert.deepEqual(model.submission(), { value: spec.value, actions: [] });
    }
  }
});

test('buttons inside list items read and write only the item state', () => {
  const spec = fixture('counter');
  spec.value = ['1', '10'];
  spec.form = { kind: 'list', path: [], label: 'Counters', defaultItem: '0', item: {
    kind: 'button', label: 'Double', action: { kind: 'set', path: [], value: {
      kind: 'natMul', left: project(), right: constant('2'),
    } },
  } };
  const model = createModel(spec);
  press(model, 'press', [1]);
  assert.deepEqual(model.submission(), { value: ['1', '20'], actions: [{ target: [1], action: 'press' }] });
});

test('controls carry error locations with list indices and sum tags', () => {
  const invoice = fixture('invoice');
  invoice.value = [{ description: 'A', quantity: '1', unitPrice: '5' }, { description: 'B', quantity: '0', unitPrice: '5' }];
  const model = createModel(invoice);
  const locations = model.controls().filter(control => control.kind === 'editor').map(control => control.location);
  assert.deepEqual(locations.filter(location => location[0]?.kind === 'item' && location[0].index === '1'),
    ['description', 'quantity', 'unitPrice'].map(name => [{ kind: 'item', index: '1' }, { kind: 'field', name }]));
  assert.deepEqual(model.view().children.find(child => child.kind === 'list').location, []);

  const shapes = fixture('shapes');
  shapes.value = { tag: 'rectangle', value: { width: '0', height: '2' } };
  const shape = createModel(shapes);
  assert.deepEqual(shape.controls().map(control => control.location), [[],
    [{ kind: 'constructor', tag: 'rectangle' }, { kind: 'field', name: 'width' }],
    [{ kind: 'constructor', tag: 'rectangle' }, { kind: 'field', name: 'height' }]]);
});
