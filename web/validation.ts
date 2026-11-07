export type LocationStep =
  | { kind: 'field'; name: string }
  | { kind: 'item'; index: string }
  | { kind: 'constructor'; tag: string };
export type Location = LocationStep[];
export type Targets =
  | { kind: 'global' }
  | { kind: 'locations'; locations: [Location, ...Location[]] };
export interface ValidationError { message: string; targets: Targets }
export type TargetResolution = Targets | { kind: 'invalidTarget'; location: Location };
export interface ResolvedError { message: string; targets: TargetResolution }

function unsupported(value: never): never {
  throw new Error(`Unsupported location: ${JSON.stringify(value)}`);
}

export function sameLocation(left: Location, right: Location): boolean {
  return left.length === right.length && left.every((step, index) => {
    const other = right[index];
    switch (step.kind) {
      case 'field': return other.kind === 'field' && step.name === other.name;
      case 'item': return other.kind === 'item' && step.index === other.index;
      case 'constructor': return other.kind === 'constructor' && step.tag === other.tag;
      default: return unsupported(step);
    }
  });
}
