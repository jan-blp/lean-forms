import { useEffect, useState } from 'react';
import type { LinkedEvidence, Model } from '@blp/lean-forms-react';
import type { Document } from './generated/Forms/Runtime/Viewer';

interface Selection {
  page: number;
  cellIds: number[];
}

export interface DocumentViewerProps {
  document: Document;
  highlighted: LinkedEvidence | null;
  picking: boolean;
  onPick(pick: Model.Evidence): void;
  onCancel(): void;
}

export function DocumentViewer({ document, highlighted, picking, onPick, onCancel }: DocumentViewerProps) {
  const [selection, setSelection] = useState<Selection | null>(null);
  useEffect(() => { if (!picking) setSelection(null); }, [picking]);
  const toggle = (page: number, cell: number) => setSelection(current => {
    const cellIds = current?.page === page ? current.cellIds : [];
    return { page, cellIds: cellIds.includes(cell) ? cellIds.filter(id => id !== cell) : [...cellIds, cell] };
  });
  const fill = () => {
    if (!selection) return;
    const page = document.pages.find(page => page.number === selection.page)!;
    const cellIds = [...selection.cellIds].sort((a, b) => a - b);
    const text = cellIds.map(id => page.cells.find(cell => cell.id === id)!.text).join(' ');
    onPick({ page: selection.page, cellIds, text });
  };
  return (
    <aside className={picking ? 'document picking' : 'document'} aria-label="Source document">
      {picking && <div className="pick-bar" role="toolbar" aria-label="Pick cells">
        <span>Select the cells that hold the value.</span>
        <button type="button" className="primary" data-pick="fill"
          disabled={!selection || selection.cellIds.length === 0} onClick={fill}>Fill field</button>
        <button type="button" data-pick="cancel" onClick={onCancel}>Cancel</button>
      </div>}
      {document.pages.map(page =>
        <svg key={page.number} className="page" viewBox={`0 0 ${page.width} ${page.height}`}
          aria-label={`Page ${page.number}`}>
          <rect className="sheet" width={page.width} height={page.height} />
          {page.cells.map(cell => {
            const lit = highlighted?.page === page.number && highlighted.cellIds.includes(cell.id);
            const chosen = selection?.page === page.number && selection.cellIds.includes(cell.id);
            const classes = ['cell', lit && 'highlighted', lit && highlighted.stale && 'stale', chosen && 'selected'];
            return (
              <g key={cell.id} className={classes.filter(Boolean).join(' ')} data-cell={cell.id}
                onClick={picking ? () => toggle(page.number, cell.id) : undefined}>
                <rect x={cell.x - 4} y={cell.y - 3} width={cell.width} height={cell.height + 6} rx={3} />
                <text x={cell.x} y={cell.y + 13}>{cell.text}</text>
              </g>
            );
          })}
        </svg>)}
    </aside>
  );
}
