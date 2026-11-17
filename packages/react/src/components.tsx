import { useEffect, useId, useRef, type InputHTMLAttributes } from 'react';
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

type Messages = { errors: readonly string[]; reports: readonly string[] };

/** Points an element at its `Feedback`; only errors mark it invalid. */
function described({ errors, reports }: Messages, feedback: string) {
  return {
    ...(errors.length === 0 ? {} : { 'aria-invalid': true } as const),
    ...(errors.length === 0 && reports.length === 0 ? {} : { 'aria-describedby': feedback }),
  };
}

/** Errors, then reports: messages that never block submit, such as failing server checks. */
function Feedback({ id, errors, reports }: Messages & { id: string }) {
  if (errors.length === 0 && reports.length === 0) return null;
  return (
    <div className="feedback" id={id}>
      {errors.map((error, index) =>
        <p key={`error-${index}`} className="validation-error">{error}</p>)}
      {reports.map((report, index) => <p key={`report-${index}`} className="report">{report}</p>)}
    </div>
  );
}

export function TextField(
    { name, label, kind, value, disabled, errors, reports, onCommit }: FormsReact.TextField) {
  const form = useLeanForm();
  const input = useRef<HTMLInputElement>(null);
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
    <form className="editor" noValidate onSubmit={event => { event.preventDefault(); commit(); }}>
      <label>{label}<input ref={element => {
        input.current = element;
        form.registerTarget(name, element);
      }} {...inputs[kind]} value={draft ?? value}
        disabled={disabled}
        {...described({ errors: shown, reports }, feedback)}
        onInput={kind === 'date' ? event => change(event.currentTarget) : undefined}
        onChange={kind === 'date' ? undefined : event => change(event.currentTarget)}
        onKeyUp={kind === 'date' ? event => {
          if (event.currentTarget.validity.badInput || form.draftError(name) !== undefined) {
            change(event.currentTarget);
          }
        } : undefined}
        onBlur={() => { if (form.draft(name) !== undefined) commit(); }} /></label>
      <Feedback id={feedback} errors={shown} reports={reports} />
    </form>
  );
}

export function Checkbox(
    { name, label, checked, disabled, errors, reports, onChange }: FormsReact.Checkbox) {
  const form = useLeanForm();
  const feedback = useId();
  return (
    <form className="editor" noValidate onSubmit={event => event.preventDefault()}>
      <label>{label}<input ref={element => form.registerTarget(name, element)}
        type="checkbox" checked={checked} disabled={disabled}
        {...described({ errors, reports }, feedback)}
        onChange={event => form.run(onChange, event.target.checked)} /></label>
      <Feedback id={feedback} errors={errors} reports={reports} />
    </form>
  );
}

export function Choice(
    { name, label, value, options, disabled, errors, reports, onChange }: FormsReact.Choice) {
  const form = useLeanForm();
  const feedback = useId();
  return (
    <fieldset ref={element => form.registerTarget(name,
      element?.querySelector<HTMLInputElement>('input:checked') ?? element?.querySelector('input') ?? null)}
      className="choice" {...described({ errors, reports }, feedback)}>
      <legend>{label}</legend>
      {options.map(option =>
        <label key={option.value}><input type="radio" name={name} value={option.value}
          checked={option.value === value} disabled={disabled}
          onChange={() => form.run(onChange, option.value)} />{option.label}</label>)}
      <Feedback id={feedback} errors={errors} reports={reports} />
    </fieldset>
  );
}

export function Choices(
    { name, label, values, options, disabled, errors, reports, onChange }: FormsReact.Choices) {
  const form = useLeanForm();
  const feedback = useId();
  const toggle = (value: string, checked: boolean) => form.run(onChange,
    options.map(option => option.value)
      .filter(option => option === value ? checked : values.includes(option)));
  return (
    <fieldset ref={element => form.registerTarget(name,
      element?.querySelector<HTMLInputElement>('input:checked') ?? element?.querySelector('input') ?? null)}
      className="choice" {...described({ errors, reports }, feedback)}>
      <legend>{label}</legend>
      {options.map(option =>
        <label key={option.value}><input type="checkbox" value={option.value}
          checked={values.includes(option.value)} disabled={disabled}
          onChange={event => toggle(option.value, event.target.checked)} />{option.label}</label>)}
      <Feedback id={feedback} errors={errors} reports={reports} />
    </fieldset>
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

export function Group({ label, children, errors, reports }: FormsReact.Group) {
  const feedback = useId();
  const message = <Feedback id={feedback} errors={errors} reports={reports} />;
  if (label === null) return <div className="stack"><Children components={children} />{message}</div>;
  return (
    <fieldset className="component" {...described({ errors, reports }, feedback)}>
      <legend>{label}</legend><Children components={children} />{message}
    </fieldset>
  );
}

export function Table({ label, headers, rows, footer, errors, reports }: FormsReact.Table) {
  const feedback = useId();
  return (
    <div className="table-component" {...described({ errors, reports }, feedback)}>
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
      <Feedback id={feedback} errors={errors} reports={reports} />
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
  output: Output,
  button: Button,
  tabBar: TabBar,
  group: Group,
  table: Table,
  page: Page,
};
