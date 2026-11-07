import type { Evaluator, Expr, Schema, Value } from './protocol.js';

export type LocationStep =
  | { kind: 'field'; name: string }
  | { kind: 'item'; index: string }
  | { kind: 'constructor'; tag: string };
export type Location = LocationStep[];
export type Targets =
  | { kind: 'global' }
  | { kind: 'locations'; locations: [Location, ...Location[]] };
export interface ValidationError { message: string; targets: Targets }
export type TargetResolution = Targets | { kind: 'invalidTarget'; location: Location };
export interface ResolvedError { message: string; targets: TargetResolution }

type LocationStepExpr =
  | { kind: 'field'; name: string }
  | { kind: 'item'; index: Expr }
  | { kind: 'constructor'; tag: string };
type TargetsExpr =
  | { kind: 'global' }
  | { kind: 'locations'; locations: [LocationStepExpr[], ...LocationStepExpr[][]] };
export type Checker =
  | { kind: 'pass' }
  | { kind: 'report'; message: Expr; targets: TargetsExpr }
  | { kind: 'ite'; condition: Expr; thenBranch: Checker; elseBranch: Checker }
  | { kind: 'cases'; subject: Expr; branches: Record<string, Checker> }
  | { kind: 'seq'; left: Checker; right: Checker }
  | { kind: 'each'; items: Expr; body: Checker };

function unsupported(value: never): never {
  throw new Error(`Unsupported validation expression: ${JSON.stringify(value)}`);
}

function object(value: Value): value is { [name: string]: Value } {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}

function locationTargets(locations: Location[]): Targets {
  if (locations.length === 0) throw new Error('Error locations must be nonempty.');
  return { kind: 'locations', locations: [locations[0], ...locations.slice(1)] };
}

export function runChecker(checker: Checker, schema: Schema, value: Value, evaluator: Evaluator): ResolvedError[] {
  return evaluator.runChecker(checker, schema, value);
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
    case 'locations': return { message: error.message, targets: locationTargets(error.targets.locations.map(location => [step, ...location])) };
    case 'invalidTarget': return { message: error.message, targets: { kind: 'invalidTarget', location: [step, ...error.targets.location] } };
    default: return unsupported(error.targets);
  }
}

export function validationErrors(refinement: Refinement, schema: Schema, value: Value, evaluator: Evaluator): ResolvedError[] {
  switch (refinement.kind) {
    case 'base': return [];
    case 'refine': return [...validationErrors(refinement.inner, schema, value, evaluator),
      ...runChecker(refinement.checker, schema, value, evaluator)];
    case 'list': {
      if (schema.kind !== 'list' || !Array.isArray(value)) throw new Error('Invalid list refinement.');
      return value.flatMap((item, index) => validationErrors(refinement.item, schema.element, item, evaluator)
        .map(error => prefix(error, { kind: 'item', index: index.toString() })));
    }
    case 'record': {
      if (schema.kind !== 'record' || !object(value)) throw new Error('Invalid record refinement.');
      return schema.fields.flatMap(field => validationErrors(refinement.fields[field.name], field.type, value[field.name], evaluator)
        .map(error => prefix(error, { kind: 'field', name: field.name })));
    }
    case 'sum': {
      if (schema.kind !== 'sum' || !object(value) || typeof value.tag !== 'string') throw new Error('Invalid sum refinement.');
      const tag = value.tag;
      const branch = schema.constructors.find(branch => branch.name === tag);
      if (!branch) throw new Error('Unknown constructor.');
      return validationErrors(refinement.branches[tag], branch.type, value.value, evaluator)
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
