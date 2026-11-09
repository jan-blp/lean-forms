import { useEffect, useState } from 'react';
import { defaultComponents } from './components.js';
import { Context, type Components, type LeanFormContext } from './context.js';
import type * as Wire from './protocol/Forms/Runtime/Wire.js';
import type * as FormsReact from './protocol/FormsReact.js';
import { Render } from './render.js';
import { openCompiledForm, type FormModel } from './runtime.js';

export interface LeanFormProps {
  descriptor: Wire.CompiledDescriptor;
  /** URL of the app's compiled `forms.mjs`. */
  moduleUrl: string | URL;
  /** Replaces default components. */
  components?: Partial<Components>;
  onSnapshot?(snapshot: Wire.Snapshot): void;
}

const message = (error: unknown) => error instanceof Error ? error.message : String(error);

/** Runs `descriptor` in the compiled Lean form and renders its component tree. */
export function LeanForm({ descriptor, moduleUrl, components, onSnapshot }: LeanFormProps) {
  const [model, setModel] = useState<FormModel>();
  const [failure, setFailure] = useState<string>();
  const url = String(moduleUrl);
  useEffect(() => {
    let opened: FormModel | undefined;
    let cancelled = false;
    openCompiledForm(descriptor, url).then(model => {
      if (cancelled) model.dispose();
      else setModel(opened = model);
    }, error => { if (!cancelled) setFailure(message(error)); });
    return () => { cancelled = true; opened?.dispose(); };
  }, [descriptor, url]);
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

  function send(event: Wire.Event): Wire.Snapshot {
    const next = model.send({ event: { message: event } });
    setSnapshot(next);
    const editable = editableFields(next.view);
    setDrafts(drafts => new Map([...drafts].filter(([name]) => editable.has(name))));
    for (const { url, ...request } of next.effects) void perform(url, request);
    return next;
  }

  async function perform(url: string, request: RequestInit) {
    let event: Wire.Event;
    try {
      const response = await fetch(url, request);
      event = { complete: { status: response.status, body: await response.text() } };
    } catch (error) { event = { failed: { message: message(error) } }; }
    try { send(event); } catch (error) { onFailure(error); }
  }

  /** Applies `argument` to field `name`; keeps the draft when Lean rejects it. */
  function commit(name: string, argument: unknown): Wire.Snapshot | undefined {
    const next = send({ apply: { key: name, argument } });
    if (next.rejection !== null) return undefined;
    setDrafts(drafts => withDraft(drafts, name, undefined));
    return next;
  }

  function run(action: FormsReact.Action, argument?: unknown) {
    try {
      if (action === 'reset') {
        setDrafts(new Map());
        send('reset');
      } else if (action === 'submit') {
        let current = snapshot;
        for (const [name, text] of drafts) {
          if (!editableFields(current.view).has(name)) continue;
          const next = commit(name, text);
          if (!next) return;
          current = next;
        }
        send('submit');
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

/** Names of the enabled fields that commit a draft (`onCommit`) anywhere in `value`. */
function editableFields(value: unknown, names = new Set<string>()): Set<string> {
  if (typeof value !== 'object' || value === null) return names;
  if ('onCommit' in value && 'name' in value && 'disabled' in value && value.disabled === false)
    names.add(String(value.name));
  for (const child of Object.values(value)) editableFields(child, names);
  return names;
}
