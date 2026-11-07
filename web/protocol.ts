type Binding = { key: string } & (
  | { event: 'click'; command: 'apply' | 'submit' | 'reset'; source: ''; argument: 'none' }
  | { event: 'input'; command: 'draft'; source: string; argument: 'value' }
  | { event: 'change' | 'submit'; command: 'apply'; source: string; argument: 'value' | 'checked' | 'index' }
);
export type DisplayView = {
  tag: 'header' | 'span' | 'h1' | 'section' | 'details' | 'summary' | 'pre'
    | 'div' | 'fieldset' | 'legend' | 'output' | 'p' | 'label' | 'table' | 'thead' | 'tbody' | 'tr' | 'th' | 'td'
    | 'input' | 'select' | 'option' | 'button' | 'form';
  attributes: [string, string][];
  text?: string;
  focusKey?: string;
  bindings: Binding[];
  children: (DisplayView | null)[];
} & ({ value: string; checked?: never } | { checked: boolean; value?: never } | { value?: never; checked?: never });
export type FormEvent =
  | { event: 'apply' | 'draft'; key: string; argument?: unknown }
  | { event: 'submit' | 'reset' }
  | { event: 'complete'; status: number; body: string }
  | { event: 'failed'; message: string };
export type FormRequest = ({ operation: 'event' } & FormEvent)
  | { operation: 'apply'; key: string; argument?: unknown }
  | { operation: 'reset' | 'validate' | 'inspect' }
  | { operation: 'serverError'; status: number; body: string };
export interface CompiledDescriptor { form: string; revision: string; value: unknown }
export interface FormSnapshot {
  title: string;
  view: DisplayView | null;
  render: boolean;
  focus: string | null;
  effects: { url: string; method: 'POST'; headers: Record<string, string>; body: string }[];
}
