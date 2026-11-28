import { useEffect, useLayoutEffect, useRef, useState } from 'react';
import { defaultComponents } from './components.js';
import { Context, type Components, type EvidenceHost, type LeanFormContext, type HostWidgets } from './context.js';
import type * as Wire from './protocol/Forms/Runtime/Wire.js';
import type * as FormsReact from './protocol/FormsReact.js';
import { Render } from './render.js';
import { openForm, type FormModel } from './runtime.js';

export type HttpTransport = (request: Wire.HttpEffect) => Promise<Response>;

export interface LeanFormProps {
  start: Wire.FormStart;
  /** URL of the app's compiled `forms.mjs`. */
  moduleUrl: string | URL;
  components?: Partial<Components>;
  /** Every host widget the form can show; an unregistered one fails the form. */
  hostWidgets?: HostWidgets;
  evidence?: EvidenceHost;
  /** Handles lookup and submission requests using the host app's authentication. */
  transport?: HttpTransport;
  onSnapshot?(snapshot: Wire.Snapshot): void;
}

const message = (error: unknown) => error instanceof Error ? error.message : String(error);

interface Opened {
  model: FormModel;
  key: number;
}

let opens = 0;

export function LeanForm(
    { start, moduleUrl, components, hostWidgets, evidence, transport, onSnapshot }: LeanFormProps) {
  const [opened, setOpened] = useState<Opened>();
  const [failure, setFailure] = useState<string>();
  const url = String(moduleUrl);
  useEffect(() => {
    let current: FormModel | undefined;
    let cancelled = false;
    openForm(start, url).then(model => {
      if (cancelled) model.dispose();
      else setOpened({ model: current = model, key: ++opens });
    }, error => { if (!cancelled) setFailure(message(error)); });
    return () => {
      cancelled = true;
      current?.dispose();
      setOpened(undefined);
      setFailure(undefined);
    };
  }, [start, url]);
  if (failure !== undefined) return <p className="error" role="alert">{failure}</p>;
  if (!opened) return <p role="status">Loading…</p>;
  return <OpenForm key={opened.key} model={opened.model}
    components={{ ...defaultComponents, ...components }} hostWidgets={hostWidgets ?? {}}
    evidence={evidence ?? null} transport={transport} onSnapshot={onSnapshot}
    onFailure={error => setFailure(message(error))} />;
}

interface OpenFormProps {
  model: FormModel;
  components: Components;
  hostWidgets: HostWidgets;
  evidence: EvidenceHost | null;
  transport?: HttpTransport;
  onSnapshot?(snapshot: Wire.Snapshot): void;
  onFailure(error: unknown): void;
}

interface Draft {
  text: string;
  error?: string;
}

async function defaultTransport({ url, ...request }: Wire.HttpEffect): Promise<Response> {
  return fetch(url, request);
}

function OpenForm({ model, components, hostWidgets, evidence, transport, onSnapshot, onFailure }: OpenFormProps) {
  const [opened] = useState(() => model.snapshot());
  const [snapshot, setSnapshot] = useState(opened);
  const [drafts, setDrafts] = useState<ReadonlyMap<string, Draft>>(new Map());
  const currentDrafts = useRef(drafts);
  const targets = useRef(new Map<string, HTMLElement>());
  const currentTransport = useRef(transport);
  useLayoutEffect(() => { currentTransport.current = transport; }, [transport]);
  const picking = useRef<string | null>(null);
  const unregistered = snapshot.hostWidgets.find(name => !Object.hasOwn(hostWidgets, name));
  useEffect(() => {
    if (unregistered !== undefined) onFailure(new Error(`No host widget is registered as "${unregistered}".`));
  }, [unregistered, onFailure]);
  useEffect(() => onSnapshot?.(snapshot), [snapshot, onSnapshot]);
  // The opened snapshot may already request data; Lean ignores repeated responses.
  useEffect(() => performAll(opened), [opened]);
  useEffect(() => {
    for (const effect of snapshot.effects) {
      if ('focus' in effect) targets.current.get(effect.focus.key)?.focus({ focusVisible: true });
    }
  }, [snapshot]);

  function send(event: Wire.Event): Wire.Snapshot {
    const next = model.send(event);
    setSnapshot(next);
    updateDrafts(new Map([...currentDrafts.current].filter(([name]) => next.draftFields.includes(name))));
    if (picking.current !== null && !next.pickFields.includes(picking.current)) cancelPick();
    performAll(next);
    return next;
  }

  function cancelPick() {
    picking.current = null;
    evidence?.cancelPick();
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
    const request = 'submit' in effect ? effect.submit.request
      : 'fetch' in effect ? effect.fetch.request
      : effect.call.request;
    let outcome: Wire.HttpOutcome;
    try {
      const response = await (currentTransport.current ?? defaultTransport)(request);
      outcome = { response: { status: response.status, body: await response.text() } };
    } catch (error) { outcome = { unreachable: { message: message(error) } }; }
    const event: Wire.Event = 'submit' in effect ? { submitted: { outcome } }
      : 'fetch' in effect ? { fetched: { id: effect.fetch.id, outcome } }
      : { called: { id: effect.call.id, outcome } };
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
        cancelPick();
        updateDrafts(new Map());
        send('reset');
      } else if (action === 'submit') {
        cancelPick();
        commitAllDrafts();
        send('submit');
      } else if ('press' in action) {
        if (commitDrafts()) send({ apply: { key: action.press.name, argument: null } });
      } else commit(action.apply.name, argument);
    } catch (error) { onFailure(error); }
  }

  const context: LeanFormContext = {
    components,
    hostWidgets,
    evidence,
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
    requestPick: (name, action) => {
      if (!evidence) return;
      picking.current = name;
      evidence.requestPick(pick => {
        picking.current = null;
        run(action, { pick });
      });
    },
  };
  if (unregistered !== undefined) return null;
  return <Context.Provider value={context}><Render component={snapshot.view} /></Context.Provider>;
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
