import { useEffect, useState } from 'react';
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
  /** Replaces default components. */
  components?: Partial<Components>;
  onSnapshot?(snapshot: Wire.Snapshot): void;
}

const message = (error: unknown) => error instanceof Error ? error.message : String(error);

/** Runs `start` in the compiled Lean form and renders its component tree. */
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

function OpenForm({ model, components, onSnapshot, onFailure }: OpenFormProps) {
  const [snapshot, setSnapshot] = useState(() => model.snapshot());
  const [drafts, setDrafts] = useState<ReadonlyMap<string, string>>(new Map());
  useEffect(() => onSnapshot?.(snapshot), [snapshot, onSnapshot]);
  // The opened snapshot may already request data; Lean ignores repeated responses.
  useEffect(() => performAll(model.snapshot()), [model]);

  function send(event: Wire.Event): Wire.Snapshot {
    const next = model.send({ event: { message: event } });
    setSnapshot(next);
    setDrafts(drafts => new Map([...drafts].filter(([name]) => next.draftFields.includes(name))));
    performAll(next);
    return next;
  }

  function performAll(snapshot: Wire.Snapshot) {
    for (const { url, id, ...request } of snapshot.effects) void perform(url, request, id);
  }

  /** Sends the response back as `fetched` when the effect has an `id`, else as the submission's. */
  async function perform(url: string, request: RequestInit, id: string | null) {
    let event: Wire.Event;
    try {
      const response = await fetch(url, request);
      const status = response.status, body = await response.text();
      event = id === null ? { complete: { status, body } } : { fetched: { id, status, body } };
    } catch (error) {
      event = id === null ? { failed: { message: message(error) } } : { unreachable: { id, message: message(error) } };
    }
    try { send(event); } catch (error) { onFailure(error); }
  }

  /** Applies `argument` to field `name`; keeps the draft when Lean rejects it. */
  function commit(name: string, argument: unknown): Wire.Snapshot | undefined {
    const next = send({ apply: { key: name, argument } });
    if (next.rejection !== null) return undefined;
    setDrafts(drafts => withDraft(drafts, name, undefined));
    return next;
  }

  /** Applies every editable draft; false when Lean rejects one. */
  function commitDrafts(): boolean {
    let current = snapshot;
    for (const [name, text] of drafts) {
      if (!current.draftFields.includes(name)) continue;
      const next = commit(name, text);
      if (!next) return false;
      current = next;
    }
    return true;
  }

  /** Buttons apply drafts first: they may reshape the form, e.g. remove a list item. */
  function run(action: FormsReact.Action, argument?: unknown) {
    try {
      if (action === 'reset') {
        setDrafts(new Map());
        send('reset');
      } else if (action === 'submit') {
        if (commitDrafts()) send('submit');
      } else if ('press' in action) {
        if (commitDrafts()) send({ apply: { key: action.press.name, argument: null } });
      } else commit(action.apply.name, argument);
    } catch (error) { onFailure(error); }
  }

  const context: LeanFormContext = {
    components,
    draft: name => drafts.get(name),
    setDraft: (name, text) => setDrafts(drafts => withDraft(drafts, name, text)),
    run,
  };
  return <Context value={context}><Render component={snapshot.view} /></Context>;
}

function withDraft(drafts: ReadonlyMap<string, string>, name: string, text: string | undefined) {
  const next = new Map(drafts);
  if (text === undefined) next.delete(name); else next.set(name, text);
  return next;
}
