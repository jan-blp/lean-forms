// Generated from Lean. Run npm --prefix web run generate.
export type Settings = { "fields": FieldSetting[] };
export type FieldSetting = { "key": string; "state": FieldState };
export type FieldState = "shown" | "readOnly" | "excluded";
export type Evidence = { "page": number; "cellIds": number[]; "text": string };
