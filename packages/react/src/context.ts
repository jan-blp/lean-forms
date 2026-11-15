import { createContext, useContext, type ComponentType } from 'react';
import type * as FormsReact from './protocol/FormsReact.js';

type Kinds<C> = C extends unknown ? keyof C : never;
export type Kind = Kinds<FormsReact.Component>;
export type Props<K extends Kind> = Extract<FormsReact.Component, Record<K, unknown>>[K];
/** One React component per Lean constructor; containers render nested lists with `<Children>`. */
export type Components = { [K in Kind]: ComponentType<Props<K>> };

export interface LeanFormContext {
  components: Components;
  draft(name: string): string | undefined;
  /** Records the text of field `name`; `undefined` drops the draft. */
  setDraft(name: string, text: string | undefined): void;
  run(action: FormsReact.Action, argument?: unknown): void;
}

export const Context = createContext<LeanFormContext | null>(null);

export function useLeanForm(): LeanFormContext {
  const context = useContext(Context);
  if (!context) throw new Error('useLeanForm must be used inside <LeanForm>.');
  return context;
}
