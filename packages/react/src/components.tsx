import { useId, useRef } from 'react';
import { useLeanForm, type Components } from './context.js';
import type * as FormsReact from './protocol/FormsReact.js';
import { Children } from './render.js';

function DraftField({ name, label, value, disabled, error, onCommit, numeric = false }:
    FormsReact.TextField & { numeric?: boolean }) {
  const form = useLeanForm();
  const input = useRef<HTMLInputElement>(null);
  const feedback = useId();
  return (
    <form className="editor" noValidate onSubmit={event => { event.preventDefault(); form.run(onCommit, input.current!.value); }}>
      <label>{label}<input ref={input} type="text" value={form.draft(name) ?? value} disabled={disabled}
        inputMode={numeric ? 'numeric' : undefined}
        aria-invalid={error === null ? undefined : true} aria-describedby={error === null ? undefined : feedback}
        onChange={event => form.setDraft(name, event.target.value === value ? undefined : event.target.value)} /></label>
      <button disabled={disabled}>Apply</button>
      {error !== null && <p className="validation-error" id={feedback}>{error}</p>}
    </form>
  );
}

export function TextField(props: FormsReact.TextField) {
  return <DraftField {...props} />;
}

export function NaturalField(props: FormsReact.NaturalField) {
  return <DraftField {...props} numeric />;
}

export function Checkbox({ label, checked, disabled, error, onChange }: FormsReact.Checkbox) {
  const form = useLeanForm();
  const feedback = useId();
  return (
    <form className="editor" noValidate onSubmit={event => event.preventDefault()}>
      <label>{label}<input type="checkbox" checked={checked} disabled={disabled}
        aria-invalid={error === null ? undefined : true} aria-describedby={error === null ? undefined : feedback}
        onChange={event => form.run(onChange, event.target.checked)} /></label>
      {error !== null && <p className="validation-error" id={feedback}>{error}</p>}
    </form>
  );
}

export function Choice({ name, label, value, options, disabled, error, onChange }: FormsReact.Choice) {
  const form = useLeanForm();
  const feedback = useId();
  return (
    <fieldset className="choice" aria-invalid={error === null ? undefined : true}
      aria-describedby={error === null ? undefined : feedback}>
      <legend>{label}</legend>
      {options.map(option =>
        <label key={option.value}><input type="radio" name={name} value={option.value}
          checked={option.value === value} disabled={disabled}
          onChange={() => form.run(onChange, option.value)} />{option.label}</label>)}
      {error !== null && <p className="validation-error" id={feedback}>{error}</p>}
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
      data-action={typeof onClick === 'string' ? onClick : 'apply'} onClick={() => form.run(onClick)}>{label}</button>
  );
}

export function Group({ label, children, error }: FormsReact.Group) {
  const feedback = useId();
  const message = error !== null && <p className="validation-error" id={feedback}>{error}</p>;
  if (label === null) return <div className="stack"><Children components={children} />{message}</div>;
  return (
    <fieldset className="component" aria-invalid={error === null ? undefined : true}
      aria-describedby={error === null ? undefined : feedback}>
      <legend>{label}</legend><Children components={children} />{message}
    </fieldset>
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
  naturalField: NaturalField,
  checkbox: Checkbox,
  choice: Choice,
  output: Output,
  button: Button,
  group: Group,
  page: Page,
};
