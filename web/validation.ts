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
