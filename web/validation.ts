import { evaluate, textValue } from './interpreter.js';
import type { Expr, Schema, Value } from './protocol.js';

export type LocationStep =
  | { kind: 'field'; name: string }
  | { kind: 'item'; index: string }
  | { kind: 'constructor'; tag: string };
export type Location = LocationStep[];
export type Targets =
  | { kind: 'global' }
  | { kind: 'fields'; locations: [Location, ...Location[]] };
export interface ValidationError { message: string; targets: Targets }
export type TargetResolution = Targets | { kind: 'invalidTarget'; location: Location };
export interface ResolvedError { message: string; targets: TargetResolution }

type LocationStepExpr =
  | { kind: 'field'; name: string }
  | { kind: 'item'; index: Expr }
  | { kind: 'constructor'; tag: string };
type TargetsExpr =
  | { kind: 'global' }
  | { kind: 'fields'; locations: [LocationStepExpr[], ...LocationStepExpr[][]] };
export type Checker =
  | { kind: 'pass' }
  | { kind: 'report'; message: Expr; targets: TargetsExpr }
  | { kind: 'when'; condition: Expr; body: Checker }
  | { kind: 'seq'; left: Checker; right: Checker }
  | { kind: 'each'; items: Expr; body: Checker };

function unsupported(value: never): never {
  throw new Error(`Unsupported validation expression: ${JSON.stringify(value)}`);
}

function object(value: Value): value is { [name: string]: Value } {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}

export function locationExists(location: Location, schema: Schema, value: Value): boolean {
  for (const step of location) {
    switch (step.kind) {
      case 'field': {
        if (schema.kind !== 'record' || !object(value)) return false;
        const field = schema.fields.find(field => field.name === step.name);
        if (!field || !Object.hasOwn(value, step.name)) return false;
        schema = field.type; value = value[step.name];
        break;
      }
      case 'item': {
        if (schema.kind !== 'list' || !Array.isArray(value) || !/^[0-9]+$/.test(step.index)) return false;
        const index = BigInt(step.index);
        if (index >= BigInt(value.length)) return false;
        schema = schema.element; value = value[Number(index)];
        break;
      }
      case 'constructor': {
        if (schema.kind !== 'sum' || !object(value) || value.tag !== step.tag || !Object.hasOwn(value, 'value')) return false;
        const branch = schema.constructors.find(branch => branch.name === step.tag);
        if (!branch) return false;
        schema = branch.type; value = value.value;
        break;
      }
      default: return unsupported(step);
    }
  }
  return true;
}

function fields(locations: Location[]): Targets {
  if (locations.length === 0) throw new Error('Error locations must be nonempty.');
  return { kind: 'fields', locations: [locations[0], ...locations.slice(1)] };
}

function evaluateTargets(targets: TargetsExpr, value: Value): Targets {
  switch (targets.kind) {
    case 'global': return targets;
    case 'fields': return fields(targets.locations.map(location => location.map(step => {
      switch (step.kind) {
        case 'field': return step;
        case 'item': {
          const index = textValue(evaluate(step.index, value));
          if (!/^[0-9]+$/.test(index)) throw new Error('Location index must be a natural number.');
          return { kind: 'item', index: BigInt(index).toString() };
        }
        case 'constructor': return step;
        default: return unsupported(step);
      }
    })));
    default: return unsupported(targets);
  }
}

function evaluateChecker(checker: Checker, value: Value): ValidationError[] {
  switch (checker.kind) {
    case 'pass': return [];
    case 'report': return [{ message: textValue(evaluate(checker.message, value)), targets: evaluateTargets(checker.targets, value) }];
    case 'when': {
      const condition = evaluate(checker.condition, value);
      if (typeof condition !== 'boolean') throw new Error('Validation condition must be boolean.');
      return condition ? evaluateChecker(checker.body, value) : [];
    }
    case 'seq': return [...evaluateChecker(checker.left, value), ...evaluateChecker(checker.right, value)];
    case 'each': {
      const items = evaluate(checker.items, value);
      if (!Array.isArray(items)) throw new Error('Validation iteration requires a list.');
      return items.flatMap((item, index) => evaluateChecker(checker.body, { outer: value, item, index: index.toString() }));
    }
    default: return unsupported(checker);
  }
}

export function runChecker(checker: Checker, schema: Schema, value: Value): ResolvedError[] {
  return evaluateChecker(checker, value).map(error => {
    switch (error.targets.kind) {
      case 'global': return error;
      case 'fields': {
        fields(error.targets.locations);
        const invalid = error.targets.locations.find(location => !locationExists(location, schema, value));
        return { message: error.message, targets: invalid === undefined ? error.targets
          : { kind: 'invalidTarget', location: invalid } };
      }
      default: return unsupported(error.targets);
    }
  });
}

export type Refinement =
  | { kind: 'base' }
  | { kind: 'refine'; inner: Refinement; checker: Checker }
  | { kind: 'list'; item: Refinement }
  | { kind: 'record'; fields: Record<string, Refinement> }
  | { kind: 'sum'; branches: Record<string, Refinement> };

function prefix(error: ResolvedError, step: LocationStep): ResolvedError {
  switch (error.targets.kind) {
    case 'global': return error;
    case 'fields': return { message: error.message, targets: fields(error.targets.locations.map(location => [step, ...location])) };
    case 'invalidTarget': return { message: error.message, targets: { kind: 'invalidTarget', location: [step, ...error.targets.location] } };
    default: return unsupported(error.targets);
  }
}

export function validationErrors(refinement: Refinement, schema: Schema, value: Value): ResolvedError[] {
  switch (refinement.kind) {
    case 'base': return [];
    case 'refine': return [...validationErrors(refinement.inner, schema, value),
      ...runChecker(refinement.checker, schema, value)];
    case 'list': {
      if (schema.kind !== 'list' || !Array.isArray(value)) throw new Error('Invalid list refinement.');
      return value.flatMap((item, index) => validationErrors(refinement.item, schema.element, item)
        .map(error => prefix(error, { kind: 'item', index: index.toString() })));
    }
    case 'record': {
      if (schema.kind !== 'record' || !object(value)) throw new Error('Invalid record refinement.');
      return schema.fields.flatMap(field => validationErrors(refinement.fields[field.name], field.type, value[field.name])
        .map(error => prefix(error, { kind: 'field', name: field.name })));
    }
    case 'sum': {
      if (schema.kind !== 'sum' || !object(value) || typeof value.tag !== 'string') throw new Error('Invalid sum refinement.');
      const tag = value.tag;
      const branch = schema.constructors.find(branch => branch.name === tag);
      if (!branch) throw new Error('Unknown constructor.');
      return validationErrors(refinement.branches[tag], branch.type, value.value)
        .map(error => prefix(error, { kind: 'constructor', tag }));
    }
    default: return unsupported(refinement);
  }
}

export function sameLocation(left: Location, right: Location): boolean {
  return left.length === right.length && left.every((step, index) => {
    const other = right[index];
    switch (step.kind) {
      case 'field': return other.kind === 'field' && step.name === other.name;
      case 'item': return other.kind === 'item' && step.index === other.index;
      case 'constructor': return other.kind === 'constructor' && step.tag === other.tag;
      default: return unsupported(step);
    }
  });
}
