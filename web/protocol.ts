type Location = (
  | { kind: 'field'; name: string }
  | { kind: 'item'; index: string }
  | { kind: 'constructor'; tag: string }
)[];
interface ResolvedError {
  message: string;
  targets: { kind: 'global' } | { kind: 'locations'; locations: [Location, ...Location[]] };
}
export type Value = string | number | boolean | Value[] | { [name: string]: Value };
export type Path = (string | number)[];
interface InvocationBase {
  target: Path;
  action: string;
  argument?: Value;
  index?: number;
}

export type Invocation = InvocationBase | (InvocationBase & { constructor: string });

// Compiled forms send display data and opaque control keys, never expression programs.
interface DisplayIdentity { messages?: string; key: string; id: string; target: Path; label: string; disabled: boolean }
export type DisplayControl = DisplayIdentity & (
  | { kind: 'button'; keepDrafts: boolean }
  | { kind: 'choice'; location: Location; value: string; options: string[] }
  | { kind: 'editor'; location: Location; options?: string[];
      widget: 'select' | 'checkbox' | 'textInput' | 'naturalInput' | 'dateInput' }
);
type Binding = { key: string } & (
  | { event: 'click'; command: 'apply'; source: ''; argument: 'none' }
  | { event: 'input'; command: 'draft'; source: string; argument: 'value' }
  | { event: 'change' | 'submit'; command: 'apply'; source: string; argument: 'value' | 'checked' | 'index' }
);
export type DisplayView = {
  tag: 'div' | 'fieldset' | 'legend' | 'output' | 'p' | 'label' | 'table' | 'thead' | 'tbody' | 'tr' | 'th' | 'td'
    | 'input' | 'select' | 'option' | 'button' | 'form';
  attributes: [string, string][];
  text?: string;
  focusKey?: string;
  bindings: Binding[];
  children: (DisplayView | null)[];
} & ({ value: string; checked?: never } | { checked: boolean; value?: never } | { value?: never; checked?: never });
export type Interaction = {
  status: string; error: boolean; focus: string | null; count: string; result: string | null;
} & ({ pending: false; send: false } | { pending: true; send: boolean });
export interface CompiledDescriptor { form: string; revision: string; value: Value }
export interface FormSnapshot {
  ui: Interaction;
  summary: string;
  submissionBlocked: boolean;
  title: string;
  view: DisplayView | null;
  controls: DisplayControl[];
  errors: ResolvedError[];
  submission: { value: Value; actions: Invocation[] };
}
