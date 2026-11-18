import { useEffect, useRef, useState } from 'react';
import { defaultComponents } from './components.js';
import { Context, type Components, type LeanFormContext } from './context.js';
import type * as Wire from './protocol/Forms/Runtime/Wire.js';
import type * as FormsReact from './protocol/FormsReact.js';
import { Render } from './render.js';
import { openForm, type FormModel } from './runtime.js';

export interface LeanFormProps {
  start: Wire.FormStart;
  /** URL of the app's compiled `forms.mjs`. */
  moduleUrl: string | URL;
  components?: Partial<Components>;
  onSnapshot?(snapshot: Wire.Snapshot): void;
}

const message = (error: unknown) => error instanceof Error ? error.message : String(error);

export function LeanForm({ start, moduleUrl, components, onSnapshot }: LeanFormProps) {
  const [model, setModel] = useState<FormModel>();
  const [failure, setFailure] = useState<string>();
  const url = String(moduleUrl);
  useEffect(() => {
    let opened: FormModel | undefined;
    let cancelled = false;
    openForm(start, url).then(model => {
      if (cancelled) model.dispose();
      else setModel(opened = model);
    }, error => { if (!cancelled) setFailure(message(error)); });
    return () => { cancelled = true; opened?.dispose(); };
  }, [start, url]);
  if (failure !== undefined) return <p className="error" role="alert">{failure}</p>;
  if (!model) return <p role="status">Loading…</p>;
  return <OpenForm model={model} components={{ ...defaultComponents, ...components }}
    onSnapshot={onSnapshot} onFailure={error => setFailure(message(error))} />;
}

interface OpenFormProps {
  model: FormModel;
  components: Components;
  onSnapshot?(snapshot: Wire.Snapshot): void;
  onFailure(error: unknown): void;
}

interface Draft {
  text: string;
  error?: string;
}

function OpenForm({ model, components, onSnapshot, onFailure }: OpenFormProps) {
  const [snapshot, setSnapshot] = useState(() => model.snapshot());
  const [drafts, setDrafts] = useState<ReadonlyMap<string, Draft>>(new Map());
  const currentDrafts = useRef(drafts);
  const targets = useRef(new Map<string, HTMLElement>());
  useEffect(() => onSnapshot?.(snapshot), [snapshot, onSnapshot]);
  // The opened snapshot may already request data; Lean ignores repeated responses.
  useEffect(() => performAll(model.snapshot()), [model]);
  useEffect(() => {
    for (const effect of snapshot.effects) {
      if ('focus' in effect) targets.current.get(effect.focus.key)?.focus({ focusVisible: true });
    }
  }, [snapshot]);

  function send(event: Wire.Event): Wire.Snapshot {
    const next = model.send(event);
    setSnapshot(next);
    updateDrafts(new Map([...currentDrafts.current].filter(([name]) => next.draftFields.includes(name))));
    performAll(next);
    return next;
  }

  function updateDrafts(next: ReadonlyMap<string, Draft>) {
    currentDrafts.current = next;
    setDrafts(next);
  }

  function performAll(snapshot: Wire.Snapshot) {
    for (const effect of snapshot.effects) {
      if (!('focus' in effect)) void perform(effect);
    }
  }

  async function perform(effect: Exclude<Wire.Effect, { focus: unknown }>) {
    const { url, ...request } = 'submit' in effect ? effect.submit.request : effect.fetch.request;
    let outcome: Wire.HttpOutcome;
    try {
      const response = await fetch(url, request);
      outcome = { response: { status: response.status, body: await response.text() } };
    } catch (error) { outcome = { unreachable: { message: message(error) } }; }
    const event: Wire.Event = 'submit' in effect ? { submitted: { outcome } } : { fetched: { id: effect.fetch.id, outcome } };
    try { send(event); } catch (error) { onFailure(error); }
  }

  /** Applies `argument` to field `name`; keeps the draft when Lean rejects it. */
  function commit(name: string, argument: unknown): Wire.Snapshot | undefined {
    const next = send({ apply: { key: name, argument } });
    if (next.rejection !== null) return undefined;
    updateDrafts(withDraft(currentDrafts.current, name, undefined));
    return next;
  }

  /** Applies every draft it can and reports the rest, so Lean blocks the submit and picks the focus. */
  function commitAllDrafts() {
    let current = model.snapshot();
    for (const [name, draft] of currentDrafts.current) {
      if (!current.draftFields.includes(name)) continue;
      if (draft.error !== undefined) current = send({ draft: { key: name, message: draft.error } });
      else current = commit(name, draft.text) ?? current;
    }
  }

  function commitDrafts(): boolean {
    let current = model.snapshot();
    for (const [name, draft] of currentDrafts.current) {
      if (!current.draftFields.includes(name)) continue;
      if (draft.error !== undefined) {
        targets.current.get(name)?.focus();
        return false;
      }
      const next = commit(name, draft.text);
      if (!next) {
        targets.current.get(name)?.focus();
        return false;
      }
      current = next;
    }
    return true;
  }

  /** Buttons apply drafts first: they may reshape the form, e.g. remove a list item. */
  function run(action: FormsReact.Action, argument?: unknown) {
    try {
      if (action === 'reset') {
        updateDrafts(new Map());
        send('reset');
      } else if (action === 'submit') {
        commitAllDrafts();
        send('submit');
      } else if ('press' in action) {
        if (commitDrafts()) send({ apply: { key: action.press.name, argument: null } });
      } else commit(action.apply.name, argument);
    } catch (error) { onFailure(error); }
  }

  const context: LeanFormContext = {
    components,
    draft: name => currentDrafts.current.get(name)?.text,
    draftError: name => currentDrafts.current.get(name)?.error,
    registerTarget: (name, element) => {
      if (element) targets.current.set(name, element); else targets.current.delete(name);
    },
    setDraft: (name, text, error) => {
      const previousError = currentDrafts.current.get(name)?.error;
      updateDrafts(withDraft(currentDrafts.current, name, text, error));
      // Dropping a draft also retires errors reported by Lean on a rejected commit.
      if (text === undefined || previousError !== error) {
        send({ draft: { key: name, message: error ?? null } });
      }
    },
    run,
  };
  return <Context value={context}><Render component={snapshot.view} /></Context>;
}

function withDraft(
    drafts: ReadonlyMap<string, Draft>,
    name: string,
    text: string | undefined,
    error?: string) {
  const next = new Map(drafts);
  if (text === undefined) next.delete(name); else next.set(name, { text, error });
  return next;
}
