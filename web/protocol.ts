export type Value = string | number | boolean | Value[] | { [name: string]: Value };
export type Path = string[];
export type Schema =
  | { kind: 'text' | 'natural' | 'date' | 'boolean' }
  | { kind: 'enum'; options: string[] }
  | { kind: 'list'; element: Schema }
  | { kind: 'record'; fields: { name: string; type: Schema }[] }
  | { kind: 'sum'; constructors: { name: string; type: Schema }[] };

export type Expr =
  | { kind: 'value'; value: Value }
  | { kind: 'project'; path: Path }
  | { kind: 'natAdd' | 'natSub' | 'natMul' | 'natLe' | 'textAppend' | 'enumEq' | 'dateLe' | 'and'; left: Expr; right: Expr }
  | { kind: 'natToText' | 'not'; operand: Expr }
  | { kind: 'enumLabel'; subject: Expr; options: string[] }
  | { kind: 'enumCases'; subject: Expr; branches: Expr[] }
  | { kind: 'length'; items: Expr }
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
  | { kind: 'field'; path: Path; schema: Schema; label: string; widget: Widget }
  | { kind: 'button'; label: string; action: Action }
  | { kind: 'actionWidget'; path: Path; schema: Schema; label: string; actions: Presentation[] };

export interface Specification {
  version: number;
  value: Value;
  form: Component;
}
export interface Invocation {
  target: string[];
  action: string;
  argument?: Value;
}

interface ControlIdentity {
  id: string;
  label: string;
  target: string[];
  key: string;
  disabled: boolean;
}
export type Control = ControlIdentity & (
  | { kind: 'button'; effect: Action | { kind: 'transform'; path: Path; body: Expr } }
  | { kind: 'editor'; path: Path; schema: Schema; value: Value; widget: Widget; body: Expr }
);
export type View =
  | { kind: 'stack'; label?: string | null; children: View[] }
  | { kind: 'actionWidget'; label: string; schema: Schema; value: Value; children: Control[] }
  | { kind: 'computed'; label: string; schema: Schema; value: Value }
  | { kind: 'text'; value: string }
  | Control;
