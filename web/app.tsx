import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import { LeanForm, type Wire } from '@blp/lean-forms-react';

const root = createRoot(document.querySelector('main')!);
const message = (error: unknown) => error instanceof Error ? error.message : String(error);
const setTitle = (snapshot: Wire.Snapshot) => { document.title = `Lean Forms · ${snapshot.title}`; };

try {
  const response = await fetch('/api/compiled-form');
  if (!response.ok) throw new Error('Could not load the form.');
  const descriptor = await response.json() as Wire.CompiledDescriptor;
  root.render(
    <StrictMode>
      <LeanForm descriptor={descriptor} moduleUrl={new URL('/wasm/forms.mjs', location.href)} onSnapshot={setTitle} />
    </StrictMode>);
} catch (error) {
  root.render(<p className="error" role="alert">{message(error)}</p>);
}
