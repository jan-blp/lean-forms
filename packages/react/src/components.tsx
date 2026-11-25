import { useEffect, useId, useLayoutEffect, useRef, useState, type InputHTMLAttributes, type KeyboardEvent } from 'react';
import { useLeanForm, type Components } from './context.js';
import type * as FormsReact from './protocol/FormsReact.js';
import { Children, Render } from './render.js';

const inputs = {
  plain: { type: 'text' },
  natural: { type: 'text', inputMode: 'numeric' },
  integer: { type: 'text' },
  decimal: { type: 'text', inputMode: 'decimal' },
  date: { type: 'date' },
  uuid: {
    type: 'text', className: 'uuid', spellCheck: false, autoCapitalize: 'off', autoComplete: 'off',
  },
} as const satisfies Record<FormsReact.TextKind, InputHTMLAttributes<HTMLInputElement>>;

function described(errors: readonly string[], feedback: string) {
  return errors.length === 0 ? {} : { 'aria-invalid': true, 'aria-describedby': feedback } as const;
}

function Feedback({ id, errors }: { id: string; errors: readonly string[] }) {
  if (errors.length === 0) return null;
  return (
    <div className="feedback" id={id}>
      {errors.map((error, index) => <p key={index} className="validation-error">{error}</p>)}
    </div>
  );
}

const summaries: Record<FormsReact.Tone, (checks: FormsReact.Checks) => string> = {
  attention: ({ unresolved }) => `${unresolved.length} open`,
  outdated: () => 'changed since the last check',
  resolved: () => 'all resolved',
  info: ({ info, outdatedInfo }) => `${info.length + outdatedInfo.length} optional`,
};

export function StatusMarker(checks: FormsReact.Checks) {
  const popover = useId();
  const marker = useRef<HTMLButtonElement>(null);
  const panel = useRef<HTMLSpanElement>(null);
  const items = (texts: string[], info: boolean) => texts.map(text => ({ text, info }));
  const sections = [
    { title: 'Open', items: items(checks.unresolved, false) },
    { title: 'Changed since the last check. Submit to re-check.',
      items: [...items(checks.outdated, false), ...items(checks.outdatedInfo, true)] },
    { title: 'Resolved automatically', items: items(checks.resolved, false) },
    { title: 'Approved', items: items(checks.approved, false) },
    { title: 'Optional', items: items(checks.info, false) },
  ].filter(section => section.items.length > 0);
  useLayoutEffect(() => {
    const element = panel.current!;
    // Use native popover attributes and events for React 18 compatibility.
    marker.current!.setAttribute('popovertarget', popover);
    element.setAttribute('popover', 'auto');
    const place = () => {
      if (!element.matches(':popover-open')) return;
      const { left, top, bottom } = marker.current!.getBoundingClientRect();
      // Measure at the left edge, where the panel does not shrink.
      element.style.left = '0px';
      element.style.top = '16px';
      const { clientWidth: width, clientHeight: height } = document.documentElement;
      element.style.left = `${Math.max(16, Math.min(left, width - element.offsetWidth - 16))}px`;
      const panelHeight = element.offsetHeight;
      const preferredTop = bottom + 4 + panelHeight <= height - 16
        ? bottom + 4 : top - 4 - panelHeight;
      element.style.top = `${Math.max(16, Math.min(preferredTop, height - panelHeight - 16))}px`;
    };
    element.addEventListener('toggle', place);
    return () => element.removeEventListener('toggle', place);
  }, [popover]);
  return (
    <div className="status">
      <button ref={marker} type="button" className={`status-marker ${checks.tone}`}>
        Checks: {summaries[checks.tone](checks)}</button>
      <span ref={panel} id={popover} className="checks">
        {sections.map(({ title, items }) => <span key={title} className="checks-section">
          <span className="checks-title">{title}</span>
          <span role="list">{items.map(({ text, info }, index) =>
            <span key={index} role="listitem" className="check">
              {text}{info && <span className="tag">Optional</span>}
            </span>)}</span>
        </span>)}
      </span>
    </div>
  );
}

function evidenceStatus(evidence: Exclude<FormsReact.Evidence, 'unsupported'>) {
  if (evidence === 'missing') return { tone: 'missing', text: 'Not linked to the document' };
  if (evidence.linked.stale) return { tone: 'stale', text: 'Changed since it was picked' };
  return { tone: 'linked', text: `From page ${evidence.linked.page}` };
}

function Evidence({ evidence, disabled, onPick }: {
  evidence: Exclude<FormsReact.Evidence, 'unsupported'>;
  disabled: boolean;
  onPick?: () => void;
}) {
  const { tone, text } = evidenceStatus(evidence);
  return (
    <div className="evidence">
      <span className={`evidence-status ${tone}`}>{text}</span>
      {onPick && <button type="button" className="pick" disabled={disabled} onClick={onPick}>
        Pick from document</button>}
    </div>
  );
}

/** Shows the field's cells while it is hovered or focused, and its evidence with a pick button. */
function useEvidence(
    name: string,
    evidence: FormsReact.Evidence,
    disabled: boolean,
    action: FormsReact.Action) {
  const form = useLeanForm();
  const host = form.evidence;
  const hostRef = useRef(host);
  hostRef.current = host;
  const linked = typeof evidence === 'object' ? evidence.linked : null;
  const pointer = useRef({ hovered: false, focused: false });
  const hover = (on: boolean) => { pointer.current.hovered = on; host?.hover(on ? linked : null); };
  const focus = (on: boolean) => { pointer.current.focused = on; host?.focus(on ? linked : null); };
  // A pick or an edit can change the cells, or their staleness, while the field is shown.
  const linkedKey = JSON.stringify(linked);
  useLayoutEffect(() => {
    if (pointer.current.hovered) hostRef.current?.hover(linked);
    if (pointer.current.focused) hostRef.current?.focus(linked);
  }, [linkedKey]);
  useEffect(() => () => {
    if (pointer.current.hovered) hostRef.current?.hover(null);
    if (pointer.current.focused) hostRef.current?.focus(null);
  }, []);
  const tracking = host && evidence !== 'unsupported' ? {
    onMouseEnter: () => hover(true),
    onMouseLeave: () => hover(false),
    onFocus: () => focus(true),
    onBlur: () => focus(false),
  } : {};
  const status = evidence === 'unsupported' ? null
    : <Evidence evidence={evidence} disabled={disabled}
      onPick={host ? () => form.requestPick(name, action) : undefined} />;
  return { tracking, status };
}

export function TextField(
    { name, label, kind, value, disabled, errors, evidence, onCommit }: FormsReact.TextField) {
  const form = useLeanForm();
  const { tracking, status } = useEvidence(name, evidence, disabled, onCommit);
  const input = useRef<HTMLInputElement | null>(null);
  const feedback = useId();
  const draft = form.draft(name);
  const draftError = form.draftError(name);
  const shown = draftError === undefined ? errors : [draftError];
  const commit = () => {
    if (form.draftError(name) === undefined && !input.current!.validity.badInput) {
      form.run(onCommit, input.current!.value);
    }
  };
  const change = (input: HTMLInputElement) => {
    const text = input.value;
    const error = input.validity.badInput
      ? input.validationMessage || 'Enter a complete value.' : undefined;
    form.setDraft(name, text === value && error === undefined ? undefined : text, error);
    if (kind === 'date' && error === undefined && text !== '' && text !== value) form.run(onCommit, text);
  };
  useEffect(() => {
    // Reset must also clear incomplete date segments, whose value is already empty.
    if (draft === undefined && input.current!.validity.badInput) input.current!.value = value;
  }, [draft, value]);
  // Enter submits the form; leaving the field applies a pending edit.
  // A picked date applies at once; the date input reports "" while a typed date is incomplete.
  return (
    <form className="editor" noValidate onSubmit={event => { event.preventDefault(); commit(); }}
      {...tracking}>
      <label>{label}<input ref={element => {
        input.current = element;
        form.registerTarget(name, element);
      }} {...inputs[kind]} value={draft ?? value}
        disabled={disabled}
        {...described(shown, feedback)}
        onInput={kind === 'date' ? event => change(event.currentTarget) : undefined}
        onChange={kind === 'date' ? undefined : event => change(event.currentTarget)}
        onKeyUp={kind === 'date' ? event => {
          if (event.currentTarget.validity.badInput || form.draftError(name) !== undefined) {
            change(event.currentTarget);
          }
        } : undefined}
        onBlur={() => { if (form.draft(name) !== undefined) commit(); }} /></label>
      <Feedback id={feedback} errors={shown} />
      {status}
    </form>
  );
}

export function Checkbox(
    { name, label, checked, disabled, errors, evidence, onChange }: FormsReact.Checkbox) {
  const form = useLeanForm();
  const { tracking, status } = useEvidence(name, evidence, disabled, onChange);
  const feedback = useId();
  return (
    <form className="editor" noValidate onSubmit={event => event.preventDefault()} {...tracking}>
      <label>{label}<input ref={element => form.registerTarget(name, element)}
        type="checkbox" checked={checked} disabled={disabled}
        {...described(errors, feedback)}
        onChange={event => form.run(onChange, event.target.checked)} /></label>
      <Feedback id={feedback} errors={errors} />
      {status}
    </form>
  );
}

export function Choice(
    { name, label, value, options, disabled, errors, onChange }: FormsReact.Choice) {
  const form = useLeanForm();
  const feedback = useId();
  return (
    <fieldset ref={element => form.registerTarget(name,
      element?.querySelector<HTMLInputElement>('input:checked') ?? element?.querySelector('input') ?? null)}
      className="choice" {...described(errors, feedback)}>
      <legend>{label}</legend>
      {options.map(option =>
        <label key={option.value}><input type="radio" name={name} value={option.value}
          checked={option.value === value} disabled={disabled}
          onChange={() => form.run(onChange, option.value)} />{option.label}</label>)}
      <Feedback id={feedback} errors={errors} />
    </fieldset>
  );
}

export function Choices(
    { name, label, values, options, disabled, errors, evidence, onChange }: FormsReact.Choices) {
  const form = useLeanForm();
  const { tracking, status } = useEvidence(name, evidence, disabled, onChange);
  const feedback = useId();
  const toggle = (value: string, checked: boolean) => form.run(onChange,
    options.map(option => option.value)
      .filter(option => option === value ? checked : values.includes(option)));
  return (
    <fieldset ref={element => form.registerTarget(name,
      element?.querySelector<HTMLInputElement>('input:checked') ?? element?.querySelector('input') ?? null)}
      className="choice" {...described(errors, feedback)} {...tracking}>
      <legend>{label}</legend>
      {options.map(option =>
        <label key={option.value}><input type="checkbox" value={option.value}
          checked={values.includes(option.value)} disabled={disabled}
          onChange={event => toggle(option.value, event.target.checked)} />{option.label}</label>)}
      <Feedback id={feedback} errors={errors} />
      {status}
    </fieldset>
  );
}

const searchPause = 300;

function foundOptions(search: FormsReact.Search | null): FormsReact.LookupOption[] {
  return search !== null && typeof search.results === 'object' && 'found' in search.results
    ? search.results.found.options : [];
}

function SearchNote({ search, label }: { search: FormsReact.Search; label: string }) {
  const { results } = search;
  if (results === 'loading') return <p className="lookup-note" role="status">Searching…</p>;
  if ('failed' in results) {
    return <p className="lookup-note validation-error">Could not search: {results.failed.message}</p>;
  }
  if (results.found.more) return <p className="lookup-note">Keep typing to narrow the list.</p>;
  if (results.found.options.length === 0) return <p className="lookup-note">No matches. Choose a listed {label.toLowerCase()}.</p>;
  return null;
}

export function Lookup({ name, label, picked, search, disabled, errors, onChange }: FormsReact.Lookup) {
  const form = useLeanForm();
  const feedback = useId();
  const list = useId();
  const [typed, setTyped] = useState<string | null>(null);
  const [active, setActive] = useState(0);
  const current = typed === null || typed === search?.text;
  const options = current ? foundOptions(search) : [];
  const optionKeys = JSON.stringify(options.map(option => [option.value, option.disabledReason]));
  const firstEnabled = options.findIndex(option => option.disabledReason === null);
  const activeIndex = options[active]?.disabledReason === null ? active : firstEnabled;
  useEffect(() => setActive(firstEnabled), [optionKeys, firstEnabled]);
  const send = (command: FormsReact.LookupInput) => form.run(onChange, { lookup: command });
  // An effect, not a timer set in the handler, so a remount (e.g. StrictMode's) re-arms it.
  useEffect(() => {
    if (current) return;
    const timer = window.setTimeout(() => send({ search: { text: typed } }), searchPause);
    return () => window.clearTimeout(timer);
  }, [typed, current]);
  const choose = (option: FormsReact.LookupOption) => {
    if (disabled || option.disabledReason !== null) return;
    setTyped(null);
    send({ choose: { key: option.value } });
  };
  const clear = () => {
    setTyped(null);
    send('clear');
  };
  const close = () => {
    setTyped(null);
    if (search !== null) send('close');
  };
  const optionId = (index: number) => `${list}-${index}`;
  const move = (direction: -1 | 1) => {
    for (let index = activeIndex + direction; index >= 0 && index < options.length; index += direction) {
      if (options[index].disabledReason === null) {
        setActive(index);
        return;
      }
    }
  };
  const keyDown = (event: KeyboardEvent<HTMLInputElement>) => {
    if (event.key === 'ArrowDown') {
      event.preventDefault();
      if (search === null) send({ search: { text: typed ?? '' } });
      else move(1);
    } else if (event.key === 'ArrowUp') {
      event.preventDefault();
      move(-1);
    } else if (event.key === 'Enter') {
      event.preventDefault();
      const option = options[activeIndex];
      if (option) choose(option);
    } else if (event.key === 'Escape' && (search !== null || typed !== null)) {
      event.preventDefault();
      close();
    }
  };
  const open = search !== null;
  return (
    <div className="editor lookup">
      <label>{label}<input ref={element => form.registerTarget(name, element)} type="text"
        role="combobox" aria-expanded={open} aria-controls={list} aria-autocomplete="list"
        aria-activedescendant={open && options[activeIndex] ? optionId(activeIndex) : undefined}
        autoComplete="off" spellCheck={false} disabled={disabled}
        value={typed ?? search?.text ?? picked?.label ?? ''}
        placeholder={picked === null ? 'Type to search' : undefined}
        {...described(errors, feedback)}
        onFocus={event => event.currentTarget.select()}
        onChange={event => setTyped(event.currentTarget.value)}
        onKeyDown={keyDown}
        onBlur={close} /></label>
      {picked !== null && !disabled &&
        <button type="button" className="clear" onClick={clear}>Clear</button>}
      {open && <div className="lookup-results">
        <ul id={list} role="listbox" aria-label={label}>
          {options.map((option, index) =>
            <li key={option.value} id={optionId(index)} role="option"
              aria-label={option.label}
              aria-describedby={option.disabledReason !== null ? `${optionId(index)}-reason` : undefined}
              aria-selected={index === activeIndex}
              aria-disabled={option.disabledReason !== null || disabled}
              onMouseDown={event => event.preventDefault()}
              onMouseEnter={() => { if (option.disabledReason === null) setActive(index); }}
              onClick={() => choose(option)}>{option.label}
              {option.disabledReason !== null &&
                <span id={`${optionId(index)}-reason`} className="lookup-disabled-reason">
                  {option.disabledReason}
                </span>}
            </li>)}
        </ul>
        {current ? <SearchNote search={search} label={label} />
          : <p className="lookup-note" role="status">Searching…</p>}
      </div>}
      <Feedback id={feedback} errors={errors} />
    </div>
  );
}

export function Output({ label, value }: FormsReact.Output) {
  return <div className="computed"><label>{label}<output>{value}</output></label></div>;
}

export function Button({ label, variant, disabled, onClick }: FormsReact.Button) {
  const form = useLeanForm();
  return (
    <button type="button" className={variant === 'primary' ? 'primary' : undefined} disabled={disabled}
      data-action={typeof onClick === 'string' ? onClick : 'press'} onClick={() => form.run(onClick)}>{label}</button>
  );
}

export function TabBar({ label, active, labels, disabled, onChange }: FormsReact.TabBar) {
  const form = useLeanForm();
  return (
    <div className="tab-bar" role="tablist" aria-label={label}>
      {labels.map((tab, index) =>
        <button key={index} type="button" role="tab" aria-selected={index === active} disabled={disabled}
          onClick={() => { if (index !== active) form.run(onChange, String(index)); }}>{tab}</button>)}
    </div>
  );
}

export function Group({ label, children, errors }: FormsReact.Group) {
  const feedback = useId();
  const message = <Feedback id={feedback} errors={errors} />;
  if (label === null) {
    return <div className="stack"><Children components={children} />{message}</div>;
  }
  return (
    <fieldset className="component" {...described(errors, feedback)}>
      <legend>{label}</legend><Children components={children} />{message}
    </fieldset>
  );
}

export function Table({ label, headers, rows, footer, errors }: FormsReact.Table) {
  const feedback = useId();
  return (
    <div className="table-component" {...described(errors, feedback)}>
      <div className="table-scroll" tabIndex={0} role="region" aria-label={label}>
        <table>
          <caption>{label}</caption>
          <thead><tr>{headers.map((header, index) => <th key={index} scope="col">{header}</th>)}</tr></thead>
          <tbody>{rows.map(row =>
            <tr key={row.key} aria-label={row.label} aria-selected={row.selected ?? undefined}
              className={row.selected ? 'selected' : undefined}>{row.cells.map((cell, column) =>
              <td key={column}><Children components={[cell]} /></td>)}</tr>)}</tbody>
        </table>
      </div>
      {rows.length === 0 && <p className="empty">No items.</p>}
      <Feedback id={feedback} errors={errors} />
      <Render component={footer} />
    </div>
  );
}

export function Page({ title, busy, body, toolbar, notice, result }: FormsReact.Page) {
  const error = 'error' in notice;
  return (
    <div>
      <header><span className="brand">LEAN FORMS</span></header>
      <h1 id="title">{title}</h1>
      <section id="controls" aria-label="Form controls" aria-busy={busy} data-runtime="compiled"><Children components={body} /></section>
      <div className="toolbar"><Children components={toolbar} /></div>
      <p id="status" role="status" aria-live="polite" className={error ? 'error' : undefined}>
        {error ? notice.error.message : notice.info.message}
      </p>
      <details id="result" hidden={result === null}><summary>Submitted value</summary><pre>{result ?? ''}</pre></details>
    </div>
  );
}

export const defaultComponents: Components = {
  textField: TextField,
  checkbox: Checkbox,
  choice: Choice,
  choices: Choices,
  lookup: Lookup,
  output: Output,
  button: Button,
  tabBar: TabBar,
  group: Group,
  table: Table,
  page: Page,
  statusMarker: StatusMarker,
};
