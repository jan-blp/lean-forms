import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import { LeanForm, type Wire } from '@blp/lean-forms-react';
import { routes } from './generated/routes';

const root = createRoot(document.querySelector('main')!);
const message = (error: unknown) => error instanceof Error ? error.message : String(error);
const setTitle = (snapshot: Wire.Snapshot) => { document.title = `Lean Forms · ${snapshot.title}`; };

try {
  const response = await fetch(routes.compiledSpecification);
  if (!response.ok) throw new Error('Could not load the form.');
  const descriptor = await response.json() as Wire.CompiledDescriptor;
  root.render(
    <StrictMode>
      <LeanForm descriptor={descriptor} moduleUrl={new URL(routes.wasmLoader, location.href)} onSnapshot={setTitle} />
    </StrictMode>);
} catch (error) {
  root.render(<p className="error" role="alert">{message(error)}</p>);
}
