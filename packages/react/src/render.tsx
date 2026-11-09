import type { ComponentType, ReactNode } from 'react';
import { useLeanForm, type Kind, type Props } from './context.js';
import type * as FormsReact from './protocol/FormsReact.js';

/** The only place where the Lean component tree becomes React elements. */
export function Render({ component }: { component: FormsReact.Component }): ReactNode {
  const { components } = useLeanForm();
  const [kind, props] = entry(component);
  const Component = components[kind] as ComponentType<object>;
  return <Component {...props} />;
}

/** Renders a nested component list, e.g. a group's `children`. */
export function Children({ components }: { components: FormsReact.Component[] }) {
  return components.map((component, index) => <Render key={key(component, index)} component={component} />);
}

function entry(component: FormsReact.Component): [Kind, object] {
  return Object.entries(component)[0] as [Kind, object];
}

/** Whether the `name` prop identifies a kind; checked against the generated props. */
const named = {
  textField: true,
  naturalField: true,
  checkbox: true,
  choice: true,
  output: false,
  button: false,
  group: false,
  page: false,
} as const satisfies { [K in Kind]: Props<K> extends { name: string } ? true : false };

/** Fields keep their identity, and focus, when siblings appear or disappear. */
function key(component: FormsReact.Component, index: number): string {
  const [kind, props] = entry(component);
  return named[kind] ? `${kind}:${(props as { name: string }).name}` : `${kind}#${index}`;
}
