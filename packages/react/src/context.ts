import { createContext, useContext, type ComponentType } from 'react';
import type * as FormsReact from './protocol/FormsReact.js';

type Kinds<C> = C extends unknown ? keyof C : never;
/** The constructor names of `FormsReact.Component`, e.g. `"textField"`. */
export type Kind = Kinds<FormsReact.Component>;
/** The props Lean sends for components of kind `K`. */
export type Props<K extends Kind> = Extract<FormsReact.Component, Record<K, unknown>>[K];
/** One React component per Lean constructor; containers render nested lists with `<Children>`. */
export type Components = { [K in Kind]: ComponentType<Props<K>> };

export interface LeanFormContext {
  components: Components;
  /** The unapplied text of field `name`, if any. */
  draft(name: string): string | undefined;
  /** Records the text of field `name`; `undefined` drops the draft. */
  setDraft(name: string, text: string | undefined): void;
  /** Performs `action`; `apply` sends `argument` to Lean. */
  run(action: FormsReact.Action, argument?: unknown): void;
}

export const Context = createContext<LeanFormContext | null>(null);

export function useLeanForm(): LeanFormContext {
  const context = useContext(Context);
  if (!context) throw new Error('useLeanForm must be used inside <LeanForm>.');
  return context;
}
