import type { Location, Refinement, ResolvedError } from './validation.js';
export type Value = string | number | boolean | Value[] | { [name: string]: Value };
export type Path = (string | number)[];
export type Schema =
  | { kind: 'text' | 'natural' | 'date' | 'boolean' }
  | { kind: 'enum'; options: string[] }
  | { kind: 'list'; element: Schema }
  | { kind: 'record'; fields: { name: string; type: Schema }[] }
  | { kind: 'sum'; constructors: { name: string; type: Schema }[] };

export type Expr =
  | { kind: 'value'; value: Value }
  | { kind: 'project'; path: Path }
  | { kind: 'natAdd' | 'natSub' | 'natMul' | 'natLe' | 'textAppend' | 'textEq' | 'enumEq' | 'dateLe' | 'and'; left: Expr; right: Expr }
  | { kind: 'natToText' | 'not'; operand: Expr }
  | { kind: 'enumLabel'; subject: Expr; options: string[] }
  | { kind: 'enumCases'; subject: Expr; branches: Expr[] }
  | { kind: 'length'; items: Expr }
  | { kind: 'all'; items: Expr; predicate: Expr; context: Path }
  | { kind: 'filter'; items: Expr; predicate: Expr }
  | { kind: 'sortBy' | 'sortNatBy'; items: Expr; key: Expr; descending: boolean }
  | { kind: 'search'; items: Expr; key: Expr; query: Expr }
  | { kind: 'snoc'; items: Expr; value: Expr }
  | { kind: 'cases'; subject: Expr; branches: Record<string, Expr> }
  | { kind: 'sum'; items: Expr; expression: Expr }
  | { kind: 'ifThenElse'; condition: Expr; whenTrue: Expr; whenFalse: Expr };

export type Widget = 'textInput' | 'naturalInput' | 'checkbox' | 'dateInput' | 'select';
export type Action = { kind: 'set'; path: Path; value: Expr };
export type Presentation = { id: string; label: string } & (
  | { kind: 'button'; body: Expr }
  | { kind: 'editor'; widget: Widget; body: Expr }
);
export type Component =
  | { kind: 'stack'; label?: string | null; children: Component[]; childIds: string[] }
  | { kind: 'visibleWhen' | 'disabledWhen'; condition: Expr; body: Component }
  | { kind: 'computed'; label: string; type: Schema; expression: Expr }
  | { kind: 'text'; expression: Expr }
  | { kind: 'table'; rows: Expr; columns: { label: string; expression: Expr }[] }
  | { kind: 'list'; path: Path; label: string; item: Component; defaultItem: Value }
  | { kind: 'sum'; path: Path; label: string; schema: Extract<Schema, { kind: 'sum' }>; branches: Record<string, Component>; defaults: Record<string, Value> }
  | { kind: 'field'; path: Path; schema: Schema; label: string; widget: Widget }
  | { kind: 'button'; label: string; action: Action }
  | { kind: 'actionWidget'; path: Path; schema: Schema; label: string; actions: Presentation[] };

export interface Specification {
  version: number;
  schema: Schema;
  validation: Refinement;
  value: Value;
  form: Component;
}
interface InvocationBase {
  target: Path;
  action: string;
  argument?: Value;
  index?: number;
}

export type Invocation = InvocationBase | (InvocationBase & { constructor: string });

interface ControlIdentity {
  id: string;
  label: string;
  target: Path;
  key: string;
  disabled: boolean;
  scope: Path;
}
export type Control = ControlIdentity & (
  | { kind: 'button'; effect: Action | { kind: 'transform'; path: Path; body: Expr }
      | { kind: 'appendDefault'; path: Path; defaultItem: Value }
      | { kind: 'remove'; path: Path; index: number } }
  | { kind: 'choice'; path: Path; location: Location; value: string; options: string[]; defaults: Record<string, Value> }
  | { kind: 'editor'; path: Path; location: Location; schema: Schema; value: Value; widget: Widget; body: Expr }
);
export type View =
  | { kind: 'stack'; label?: string | null; children: View[] }
  | { kind: 'actionWidget'; location: Location; label: string; schema: Schema; value: Value; children: Control[] }
  | { kind: 'computed'; label: string; schema: Schema; value: Value }
  | { kind: 'text'; value: string }
  | { kind: 'table'; columns: string[]; rows: string[][] }
  | { kind: 'list'; location: Location; label: string; items: { body: View | null; remove: Control }[]; append: Control }
  | { kind: 'sum'; selector: Control; body: View | null }
  | Control;

export type ValidationError = ResolvedError;

export type SubmissionError =
  | { kind: 'validation'; message: string; errors: ValidationError[] }
  | { kind: 'replay' | 'request'; message: string };
