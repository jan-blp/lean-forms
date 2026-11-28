import { createContext, useContext, type ComponentType } from 'react';
import type * as FormsReact from './protocol/FormsReact.js';
import type { Evidence } from './protocol/Forms/Model.js';

type Kinds<C> = C extends unknown ? keyof C : never;
export type Kind = Kinds<FormsReact.Component>;
export type Props<K extends Kind> = Extract<FormsReact.Component, Record<K, unknown>>[K];
/** One React component per Lean constructor; containers render nested lists with `<Children>`. */
export type Components = { [K in Kind]: ComponentType<Props<K>> };

/** What a host widget receives: Lean's `Input`, and `onChange` to send back an `Output`. */
export interface HostWidgetProps<Input, Output> {
  input: Input;
  disabled: boolean;
  onChange(output: Output): void;
}

export type HostWidgetComponent = ComponentType<HostWidgetProps<unknown, unknown>>;

/** Types a host widget by the `Input` and `Output` of its Lean contract. */
export function hostWidget<Input, Output>(
    component: ComponentType<HostWidgetProps<Input, Output>>): HostWidgetComponent {
  return component as HostWidgetComponent;
}

/** Host widgets by the `name` of their Lean contract. */
export type HostWidgets = Readonly<Record<string, HostWidgetComponent>>;

/** Where focus goes for a control: an element, or a host widget's first focusable element. */
export type FocusTarget = Pick<HTMLElement, 'focus'>;

export type LinkedEvidence = Extract<FormsReact.Evidence, { linked: unknown }>['linked'];

export interface EvidenceHost {
  /** Shows the cells of the field under the pointer; `null` when it leaves or has none. */
  hover(evidence: LinkedEvidence | null): void;
  /** Shows the cells of the focused field; `null` when focus leaves or it has none. */
  focus(evidence: LinkedEvidence | null): void;
  /** Hands the next cells picked on the document to `fill`. */
  requestPick(fill: (pick: Evidence) => void): void;
  /** Drops the pending request, if any. */
  cancelPick(): void;
}

export interface LeanFormContext {
  components: Components;
  hostWidgets: HostWidgets;
  evidence: EvidenceHost | null;
  draft(name: string): string | undefined;
  draftError(name: string): string | undefined;
  registerTarget(name: string, target: FocusTarget | null): void;
  /** Records the text of field `name`; `undefined` drops the draft. */
  setDraft(name: string, text: string | undefined, error?: string): void;
  run(action: FormsReact.Action, argument?: unknown): void;
  /** Lets the evidence host fill field `name` with the next pick, through `action`. */
  requestPick(name: string, action: FormsReact.Action): void;
}

export const Context = createContext<LeanFormContext | null>(null);

export function useLeanForm(): LeanFormContext {
  const context = useContext(Context);
  if (!context) throw new Error('useLeanForm must be used inside <LeanForm>.');
  return context;
}
