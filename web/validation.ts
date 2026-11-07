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

export function runChecker(checker: Checker, schema: Schema, value: Value, evaluator: Evaluator): ResolvedError[] {
  return evaluator.runChecker(checker, schema, value);
}

export type Refinement =
  | { kind: 'base' }
  | { kind: 'refine'; inner: Refinement; checker: Checker }
  | { kind: 'list'; item: Refinement }
  | { kind: 'record'; fields: Record<string, Refinement> }
  | { kind: 'sum'; branches: Record<string, Refinement> };

export function validationErrors(refinement: Refinement, schema: Schema, value: Value, evaluator: Evaluator): ResolvedError[] {
  return evaluator.validate(refinement, schema, value);
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
