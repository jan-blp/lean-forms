import { hostWidget, type HostWidgets } from '@blp/lean-forms-react';
import type { PickerInput, PickerOutput } from './generated/Forms/ExampleForms/Swatches';

const SwatchPicker = hostWidget<PickerInput, PickerOutput>(({ input, disabled, onChange }) => (
  <div className="swatches" role="radiogroup">
    {input.swatches.map(swatch =>
      <button key={swatch.id} type="button" role="radio" className="swatch" disabled={disabled}
        aria-checked={swatch.id === input.selected} aria-label={swatch.label} title={swatch.label}
        style={{ background: swatch.color }} onClick={() => onChange({ id: swatch.id })} />)}
  </div>
));

export const hostWidgets: HostWidgets = { swatchPicker: SwatchPicker };
