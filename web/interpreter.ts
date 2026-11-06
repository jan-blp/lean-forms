import type { Location } from './validation.js';
import { validationErrors } from './validation.js';
import type { Component, Control, Evaluator, Expr, Invocation, Path, Presentation, Schema, Specification, Value, View } from './protocol.js';

function natural(value: unknown) {
  if (typeof value !== 'string' || !/^[0-9]+$/.test(value)) {
    throw new Error('Enter a non-negative whole number.');
  }
  return BigInt(value);
}

export function get(value: Value, path: Path): Value {
  return path.reduce((current, name) => typeof name === 'number' ? array(current)[name] : record(current)[name], value);
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
  const parent = get(result, path.slice(0, -1));
  const last = path[path.length - 1];
  if (typeof last === 'number') array(parent)[last] = structuredClone(replacement);
  else record(parent)[last] = structuredClone(replacement);
  return result;
}

// Lean compares Unicode scalar values and lowercases ASCII only.
function compareText(left: string, right: string): number {
  const a = Array.from(left, char => char.codePointAt(0)!);
  const b = Array.from(right, char => char.codePointAt(0)!);
  for (let i = 0; i < Math.min(a.length, b.length); i++) {
    if (a[i] !== b[i]) return a[i] - b[i];
  }
  return a.length - b.length;
}

function lower(text: string): string {
  return text.replace(/[A-Z]/g, char => char.toLowerCase());
}

export function evaluate(expression: Expr, current: Value): Value {
  switch (expression.kind) {
    case 'all': return array(evaluate(expression.items, current)).every((item, index) =>
      evaluate(expression.predicate, { outer: get(current, expression.context), item, index: String(index) }));
    case 'filter': return array(evaluate(expression.items, current)).filter(item => evaluate(expression.predicate, item));
    case 'snoc': return [...array(evaluate(expression.items, current)), evaluate(expression.value, current)];
    case 'cases': {
      const selected = record(evaluate(expression.subject, current));
      return evaluate(expression.branches[textValue(selected.tag)], selected.value);
    }
    case 'search': {
      const query = lower(textValue(evaluate(expression.query, current)));
      return array(evaluate(expression.items, current)).filter(item => lower(textValue(evaluate(expression.key, item))).includes(query));
    }
    case 'sortBy':
    case 'sortNatBy': {
      const rows = [...array(evaluate(expression.items, current))];
      return rows.sort((left, right) => {
        const a = evaluate(expression.key, left);
        const b = evaluate(expression.key, right);
        const order = expression.kind === 'sortBy' ? compareText(textValue(a), textValue(b))
          : natural(a) < natural(b) ? -1 : natural(a) > natural(b) ? 1 : 0;
        return expression.descending ? -order : order;
      });
    }
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
    case 'textEq': return textValue(evaluate(expression.left, current)) === textValue(evaluate(expression.right, current));
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

export const typescriptEvaluator: Evaluator = (expression, current) => ({ value: evaluate(expression, current) });

// Resolve scopes against the actual value so sum payloads use the active branch.
function schemaAt(schema: Schema, path: Path, value: Value): Schema {
  for (const step of path) {
    if (schema.kind === 'record' && typeof step === 'string') {
      const field = schema.fields.find(field => field.name === step);
      if (!field) throw new Error(`Unknown schema field: ${step}`);
      schema = field.type;
    } else if (schema.kind === 'list' && typeof step === 'number') {
      schema = schema.element;
    } else if (schema.kind === 'sum' && step === 'value') {
      const branch = schema.constructors.find(branch => branch.name === record(value).tag);
      if (!branch) throw new Error('Unknown sum constructor.');
      schema = branch.type;
    } else throw new Error('Invalid schema path.');
    value = get(value, [step]);
  }
  return schema;
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

function fieldLocation(path: Path): Location {
  return path.map(step => typeof step === 'string'
    ? { kind: 'field', name: step } : { kind: 'item', index: step.toString() });
}

export function createModel(specification: Specification, evaluator: Evaluator = typescriptEvaluator) {
  if (specification.version !== 8) throw new Error('Unsupported form specification version.');
  const spec = structuredClone(specification);
  let value = structuredClone(spec.value);
  let actions: Invocation[] = [];

  const evaluateValue = (expression: Expr, current: Value, schema?: Schema) => evaluator(expression, current, schema).value;

  function view(): View | null {
    // JSON payloads use "value"; error locations use the active constructor tag.
    function visit(component: Component, target: Path = [], disabled = false, scope: Path = [], location: Location = []): View | null {
      const current = get(value, scope);
      const currentSchema = evaluator === typescriptEvaluator ? undefined : schemaAt(spec.schema, scope, value);
      function identity(id: string, label: string, index?: number) {
        return { id, label, target, disabled, scope, key: JSON.stringify(index === undefined ? [target, id] : [target, id, index]) };
      }
      function control(action: Presentation, path: Path, schema: Schema): Control {
        const common = identity(action.id, action.label);
        switch (action.kind) {
          case 'button': return { ...common, kind: 'button', effect: { kind: 'transform', path, body: action.body } };
          case 'editor': return { ...action, ...common, path, location: [...location, ...fieldLocation(path)], schema, value: get(current, path) };
          default: return unsupported(action);
        }
      }
      switch (component.kind) {
        case 'stack':
          return { kind: 'stack', label: component.label,
            children: component.children.map((child, index) => visit(child, [...target, component.childIds[index]], disabled, scope, location))
              .filter((child): child is View => child !== null) };
        case 'visibleWhen':
          return evaluateValue(component.condition, current, currentSchema) ? visit(component.body, target, disabled, scope, location) : null;
        case 'disabledWhen':
          return visit(component.body, target, disabled || Boolean(evaluateValue(component.condition, current, currentSchema)), scope, location);
        case 'list': {
          const items = array(get(current, component.path));
          return { kind: 'list', location: [...location, ...fieldLocation(component.path)], label: component.label,
            append: { ...identity('appendDefault', 'Add item'), kind: 'button',
              effect: { kind: 'appendDefault', path: component.path, defaultItem: component.defaultItem } },
            items: items.map((_, index) => ({
              body: visit(component.item, [...target, index], disabled, [...scope, ...component.path, index],
                [...location, ...fieldLocation(component.path), { kind: 'item', index: index.toString() }]),
              remove: { ...identity('remove', 'Remove item', index), kind: 'button',
                effect: { kind: 'remove', path: component.path, index } },
            })) };
        }
        case 'sum': {
          const selected = record(get(current, component.path));
          const tag = textValue(selected.tag);
          return { kind: 'sum', selector: { ...identity('select', component.label), kind: 'choice',
            path: component.path, location: [...location, ...fieldLocation(component.path)], value: tag, options: component.schema.constructors.map(branch => branch.name), defaults: component.defaults },
            body: visit(component.branches[tag], [...target, tag], disabled, [...scope, ...component.path, 'value'],
              [...location, ...fieldLocation(component.path), { kind: 'constructor', tag }]) };
        }
        case 'table': {
          const rows = evaluator(component.rows, current, currentSchema);
          if (rows.schema && rows.schema.kind !== 'list') throw new Error('Table rows require a list.');
          const rowSchema = rows.schema?.kind === 'list' ? rows.schema.element : undefined;
          return { kind: 'table', columns: component.columns.map(column => column.label),
            rows: array(rows.value).map(row =>
              component.columns.map(column => textValue(evaluateValue(column.expression, row, rowSchema)))) };
        }
        case 'computed':
          return { kind: 'computed', label: component.label, schema: component.type,
            value: evaluateValue(component.expression, current, currentSchema) };
        case 'text':
          return { kind: 'text', value: textValue(evaluateValue(component.expression, current, currentSchema)) };
        case 'field':
          return control({ kind: 'editor', id: 'replace', label: component.label, widget: component.widget,
            body: { kind: 'project', path: ['argument'] } }, component.path, component.schema);
        case 'button':
          return { ...identity('press', component.label), kind: 'button', effect: component.action };
        case 'actionWidget':
          return { kind: 'actionWidget', location: [...location, ...fieldLocation(component.path)], label: component.label, value: get(current, component.path),
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
        case 'list': return [node.append, ...node.items.flatMap(item => [...collect(item.body), item.remove])];
        case 'sum': return [node.selector, ...collect(node.body)];
        case 'button':
        case 'choice':
        case 'editor': return [node];
        case 'computed':
        case 'table':
        case 'text': return [];
        default: return unsupported(node);
      }
    }
    return collect(view());
  }

  function apply(key: string, argument?: unknown) {
    const control = controls().find(control => control.key === key);
    if (!control || control.disabled) throw new Error('This action is unavailable.');
    let invocation: Invocation = { target: control.target, action: control.id };
    const current = get(value, control.scope);
    const currentSchema = evaluator === typescriptEvaluator ? undefined : schemaAt(spec.schema, control.scope, value);
    let next: Value;
    let path: Path;
    switch (control.kind) {
      case 'button': {
        if (argument !== undefined) throw new Error('Buttons do not accept an argument.');
        const effect = control.effect;
        path = effect.path;
        switch (effect.kind) {
          case 'set': next = evaluateValue(effect.value, current, currentSchema); break;
          case 'transform': next = evaluateValue(effect.body, get(current, path), currentSchema && schemaAt(currentSchema, path, current)); break;
          case 'appendDefault': next = [...array(get(current, path)), structuredClone(effect.defaultItem)]; break;
          case 'remove':
            invocation.index = effect.index;
            next = array(get(current, path)).filter((_, index) => index !== effect.index);
            break;
          default: return unsupported(effect);
        }
        break;
      }
      case 'choice': {
        path = control.path;
        const tag = textValue(argument);
        if (!control.options.includes(tag)) throw new Error('Unknown constructor.');
        invocation = { ...invocation, constructor: tag };
        const selected = record(get(current, path));
        next = selected.tag === tag ? selected : { tag, value: structuredClone(control.defaults[tag]) };
        break;
      }
      case 'editor': {
        path = control.path;
        const normalized = normalize(control.schema, argument);
        invocation.argument = normalized;
        next = evaluateValue(control.body, { current: get(current, path), argument: normalized }, currentSchema ? {
          kind: 'record', fields: [
            { name: 'current', type: schemaAt(currentSchema, path, current) },
            { name: 'argument', type: control.schema },
          ],
        } : undefined);
        break;
      }
      default: return unsupported(control);
    }
    value = set(value, [...control.scope, ...path], next);
    actions.push(invocation);
  }

  view();
  return {
    view,
    controls,
    apply,
    submission: () => structuredClone({ value, actions }),
    errors() { return validationErrors(spec.validation, spec.schema, value, evaluator); },
    reset() { value = structuredClone(spec.value); actions = []; },
  };
}
