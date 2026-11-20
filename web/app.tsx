import { StrictMode, useState } from 'react';
import { createRoot } from 'react-dom/client';
import { LeanForm, type EvidenceHost, type FormsReact, type LinkedEvidence, type Wire } from '@blp/lean-forms-react';
import { routes } from './generated/routes';
import type { Document } from './generated/Forms/Runtime/Viewer';
import { DocumentViewer } from './viewer';

const main = document.querySelector('main')!;
const root = createRoot(main);
const message = (error: unknown) => error instanceof Error ? error.message : String(error);
const setTitle = (snapshot: Wire.Snapshot) => { document.title = `Lean Forms · ${snapshot.title}`; };
const moduleUrl = new URL(routes.wasmLoader, location.href);

function WithDocument({ start, source }: { start: Wire.FormStart; source: Document }) {
  const [hovered, setHovered] = useState<LinkedEvidence | null>(null);
  const [focused, setFocused] = useState<LinkedEvidence | null>(null);
  const [fill, setFill] = useState<((pick: FormsReact.Pick) => void) | null>(null);
  const evidence: EvidenceHost = { hover: setHovered, focus: setFocused, arm: fill => setFill(() => fill) };
  return (
    <div className="with-document">
      <LeanForm start={start} moduleUrl={moduleUrl} evidence={evidence} onSnapshot={setTitle} />
      <DocumentViewer document={source} highlighted={hovered ?? focused} picking={fill !== null}
        onPick={pick => { setFill(null); fill?.(pick); }} onCancel={() => setFill(null)} />
    </div>
  );
}

async function load<T>(url: string): Promise<T> {
  const response = await fetch(url);
  if (!response.ok) throw new Error('Could not load the form.');
  return await response.json() as T;
}

try {
  const [start, source] = await Promise.all([
    load<Wire.FormStart>(routes.formStart),
    load<Document | null>(routes.document)]);
  main.classList.toggle('wide', source !== null);
  root.render(
    <StrictMode>
      {source === null
        ? <LeanForm start={start} moduleUrl={moduleUrl} onSnapshot={setTitle} />
        : <WithDocument start={start} source={source} />}
    </StrictMode>);
} catch (error) {
  root.render(<p className="error" role="alert">{message(error)}</p>);
}
