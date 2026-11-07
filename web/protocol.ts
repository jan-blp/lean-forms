import type { Location, ResolvedError } from './validation.js';
export type Value = string | number | boolean | Value[] | { [name: string]: Value };
export type Path = (string | number)[];
interface InvocationBase {
  target: Path;
  action: string;
  argument?: Value;
  index?: number;
}

export type Invocation = InvocationBase | (InvocationBase & { constructor: string });

// Compiled forms send display data and opaque control keys, never expression programs.
interface DisplayIdentity { messages?: string; key: string; id: string; target: Path; label: string; disabled: boolean }
export type DisplayControl = DisplayIdentity & (
  | { kind: 'button'; keepDrafts: boolean }
  | { kind: 'choice'; location: Location; value: string; options: string[] }
  | ({ kind: 'editor'; location: Location } & (
      | { widget: 'select'; value: number; options: string[] }
      | { widget: 'checkbox'; value: boolean }
      | { widget: 'textInput' | 'naturalInput' | 'dateInput'; value: string }
    ))
);
export type DisplayView = { messages?: string } & (
  | { kind: 'stack'; label?: string | null; children: DisplayView[] }
  | { kind: 'actionWidget'; location: Location; label: string; text: string; children: DisplayControl[] }
  | { kind: 'list'; location: Location; label: string; items: { body: DisplayView | null; remove: DisplayControl }[]; append: DisplayControl }
  | { kind: 'sum'; selector: DisplayControl; body: DisplayView | null }
  | { kind: 'computed'; label: string; text: string }
  | { kind: 'text'; value: string }
  | { kind: 'table'; columns: string[]; rows: string[][] }
  | DisplayControl);
export interface CompiledDescriptor { form: string; revision: string; value: Value }
export interface FormSnapshot {
  summary: string;
  submissionBlocked: boolean;
  title: string;
  view: DisplayView | null;
  controls: DisplayControl[];
  errors: ResolvedError[];
  submission: { value: Value; actions: Invocation[] };
}
