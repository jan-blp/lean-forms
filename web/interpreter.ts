import type { Component, Control, Expr, Invocation, Path, Presentation, Schema, Specification, Value, View } from './protocol.js';

function natural(value: unknown) {
  if (typeof value !== 'string' || !/^[0-9]+$/.test(value)) {
    throw new Error('Enter a non-negative whole number.');
  }
  return BigInt(value);
}

export function get(value: Value, path: Path): Value {
  return path.reduce((current, name) => record(current)[name], value);
}

export function textValue(value: unknown): string {
  if (typeof value !== 'string') throw new Error('Expected text.');
  return value;
}

function array(value: Value): Value[] {
  if (!Array.isArray(value)) throw new Error('Expected a list.');
  return value;
}

function record(value: Value): { [name: string]: Value } {
  if (typeof value !== 'object' || Array.isArray(value)) throw new Error('Expected a record.');
  return value;
}

function index(value: Value): number {
  if (typeof value !== 'number' || !Number.isInteger(value) || value < 0) throw new Error('Expected an enum index.');
  return value;
}

function unsupported(value: never): never {
  throw new Error(`Unsupported variant: ${JSON.stringify(value)}`);
}

function set(value: Value, path: Path, replacement: Value): Value {
  if (path.length === 0) return structuredClone(replacement);
  const result = structuredClone(value);
  record(get(result, path.slice(0, -1)))[path[path.length - 1]] = structuredClone(replacement);
  return result;
}

export function evaluate(expression: Expr, current: Value): Value {
  switch (expression.kind) {
    case 'value': return structuredClone(expression.value);
    case 'project': return get(current, expression.path);
    case 'natAdd': return (natural(evaluate(expression.left, current)) + natural(evaluate(expression.right, current))).toString();
    case 'natSub': {
      const result = natural(evaluate(expression.left, current)) - natural(evaluate(expression.right, current));
      return (result < 0n ? 0n : result).toString();
    }
    case 'natMul': return (natural(evaluate(expression.left, current)) * natural(evaluate(expression.right, current))).toString();
    case 'natLe': return natural(evaluate(expression.left, current)) <= natural(evaluate(expression.right, current));
    case 'natToText': return natural(evaluate(expression.operand, current)).toString();
    case 'textAppend': return textValue(evaluate(expression.left, current)) + textValue(evaluate(expression.right, current));
    case 'enumLabel': return expression.options[index(evaluate(expression.subject, current))];
    case 'enumCases': return evaluate(expression.branches[index(evaluate(expression.subject, current))], current);
    case 'enumEq': return evaluate(expression.left, current) === evaluate(expression.right, current);
    case 'dateLe': return textValue(evaluate(expression.left, current)) <= textValue(evaluate(expression.right, current));
    case 'length': return array(evaluate(expression.items, current)).length.toString();
    case 'sum': return array(evaluate(expression.items, current))
      .reduce((total, item) => total + natural(evaluate(expression.expression, item)), 0n).toString();
    case 'not': return !evaluate(expression.operand, current);
    case 'and': return evaluate(expression.left, current) && evaluate(expression.right, current);
    case 'ifThenElse': return evaluate(evaluate(expression.condition, current) ? expression.whenTrue : expression.whenFalse, current);
    default: return unsupported(expression);
  }
}

export function formatValue(schema: Schema, value: Value): string {
  switch (schema.kind) {
    case 'text':
    case 'natural':
    case 'date': return textValue(value);
    case 'boolean': return value ? 'true' : 'false';
    case 'enum': return schema.options[index(value)];
    case 'list': return '[' + array(value).map(item => formatValue(schema.element, item)).join(', ') + ']';
    case 'record': return '{' + schema.fields.map(field => `${field.name}: ${formatValue(field.type, record(value)[field.name])}`).join(', ') + '}';
    case 'sum': {
      const selected = record(value);
      const branch = schema.constructors.find(branch => branch.name === selected.tag);
      if (!branch) throw new Error('Unknown sum constructor.');
      return `${selected.tag}: ${formatValue(branch.type, selected.value)}`;
    }
    default: return unsupported(schema);
  }
}

function normalize(schema: Schema, value: unknown): Value {
  switch (schema.kind) {
    case 'natural': return natural(textValue(value).trim()).toString();
    case 'text':
      if (typeof value === 'string') return value;
      break;
    case 'boolean':
      if (typeof value === 'boolean') return value;
      break;
    case 'enum':
      if (typeof value === 'number' && Number.isInteger(value) && value >= 0 && value < schema.options.length) return value;
      break;
    case 'date': {
      if (typeof value !== 'string' || !/^[0-9]{4}-[0-9]{2}-[0-9]{2}$/.test(value)) break;
      const [year, month, day] = value.split('-').map(Number);
      const leap = year % 4 === 0 && (year % 100 !== 0 || year % 400 === 0);
      const days = [31, leap ? 29 : 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
      if (year >= 1 && month >= 1 && month <= 12 && day >= 1 && day <= days[month - 1]) return value;
      break;
    }
    default: throw new Error(`Unsupported value type: ${schema.kind}`);
  }
  throw new Error(`Invalid ${schema.kind} value.`);
}

export function createModel(specification: Specification) {
  if (specification.version !== 6) throw new Error('Unsupported form specification version.');
  const spec = structuredClone(specification);
  let value = structuredClone(spec.value);
  let actions: Invocation[] = [];

  function view(): View | null {
    function visit(component: Component, target: string[] = [], disabled = false): View | null {
      function identity(id: string, label: string) {
        return { id, label, target, disabled, key: JSON.stringify([target, id]) };
      }
      function control(action: Presentation, path: Path, schema: Schema): Control {
        const common = identity(action.id, action.label);
        switch (action.kind) {
          case 'button': return { ...common, kind: 'button', effect: { kind: 'transform', path, body: action.body } };
          case 'editor': return { ...action, ...common, path, schema, value: get(value, path) };
          default: return unsupported(action);
        }
      }
      switch (component.kind) {
        case 'stack':
          return { kind: 'stack', label: component.label,
            children: component.children.map((child, index) => visit(child, [...target, component.childIds[index]], disabled))
              .filter((child): child is View => child !== null) };
        case 'visibleWhen':
          return evaluate(component.condition, value) ? visit(component.body, target, disabled) : null;
        case 'disabledWhen':
          return visit(component.body, target, disabled || Boolean(evaluate(component.condition, value)));
        case 'computed':
          return { kind: 'computed', label: component.label, schema: component.type,
            value: evaluate(component.expression, value) };
        case 'text':
          return { kind: 'text', value: textValue(evaluate(component.expression, value)) };
        case 'field':
          return control({ kind: 'editor', id: 'replace', label: component.label, widget: component.widget,
            body: { kind: 'project', path: ['argument'] } }, component.path, component.schema);
        case 'button':
          return { ...identity('press', component.label), kind: 'button', effect: component.action };
        case 'actionWidget':
          return { kind: 'actionWidget', label: component.label, value: get(value, component.path),
            schema: component.schema, children: component.actions.map(action => control(action, component.path, component.schema)) };
        default: return unsupported(component);
      }
    }
    return structuredClone(visit(spec.form));
  }

  function controls(): Control[] {
    function collect(node: View | null): Control[] {
      if (!node) return [];
      switch (node.kind) {
        case 'stack':
        case 'actionWidget': return node.children.flatMap(collect);
        case 'button':
        case 'editor': return [node];
        case 'computed':
        case 'text': return [];
        default: return unsupported(node);
      }
    }
    return collect(view());
  }

  function apply(key: string, argument?: unknown) {
    const control = controls().find(control => control.key === key);
    if (!control || control.disabled) throw new Error('This action is unavailable.');
    const invocation: Invocation = { target: control.target, action: control.id };
    let next: Value;
    let path: Path;
    switch (control.kind) {
      case 'button': {
        if (argument !== undefined) throw new Error('Buttons do not accept an argument.');
        const effect = control.effect;
        path = effect.path;
        switch (effect.kind) {
          case 'set': next = evaluate(effect.value, value); break;
          case 'transform': next = evaluate(effect.body, get(value, path)); break;
          default: return unsupported(effect);
        }
        break;
      }
      case 'editor': {
        path = control.path;
        const normalized = normalize(control.schema, argument);
        invocation.argument = normalized;
        next = evaluate(control.body, { current: get(value, path), argument: normalized });
        break;
      }
      default: return unsupported(control);
    }
    value = set(value, path, next);
    actions.push(invocation);
  }

  view();
  return {
    view,
    controls,
    apply,
    submission: () => structuredClone({ value, actions }),
    reset() { value = structuredClone(spec.value); actions = []; },
  };
}
