// Generated from Lean. Run npm --prefix web run generate.
export type Request = { "open": { "descriptor": CompiledDescriptor } } | { "send": { "handle": string; "request": FormRequest } } | { "dispose": { "handle": string } };
export type CompiledDescriptor = { "form": string; "revision": string; "value": unknown };
export type FormRequest = { "event": { "message": FormEvent } } | { "apply": { "key": string; "argument": unknown } } | "reset" | "validate" | "inspect" | { "serverError": { "status": number; "body": string } };
export type FormEvent = { "apply": { "key": string; "argument": unknown } } | { "draft": { "key": string; "argument": string } } | "submit" | "reset" | { "complete": { "status": number; "body": string } } | { "failed": { "message": string } };
export type Success = { "ok": boolean; "value": Response };
export type Response = { "opened": { "handle": string; "snapshot": Snapshot } } | { "updated": { "snapshot": Snapshot } } | "disposed";
export type Snapshot = { "title": string; "view": DisplayView | null; "render": boolean; "focus": string | null; "effects": HttpEffect[]; "summary": string; "submissionBlocked": boolean; "controls": unknown[]; "submission": unknown; "errors": unknown[] };
export type DisplayView = { "element": { "tag": Tag; "attributes": [string, string][]; "children": (DisplayView | null)[]; "bindings": Binding[]; "text": string | null; "value": string | null; "checked": boolean | null; "focusKey": string | null } };
export type Tag = "header" | "span" | "h1" | "section" | "details" | "summary" | "pre" | "div" | "fieldset" | "legend" | "output" | "p" | "label" | "input" | "button" | "form";
export type Binding = { "event": DomEvent; "command": BindingCommand; "key": string; "source": string; "argument": DomArgument };
export type DomEvent = "click" | "input" | "change" | "submit";
export type BindingCommand = "apply" | "draft" | "submit" | "reset";
export type DomArgument = "none" | "value" | "checked";
export type HttpEffect = { "url": string; "method": HttpMethod; "headers": HttpHeaders; "body": string };
export type HttpMethod = "POST";
export type HttpHeaders = { "Content-Type": string };
export type Failure = { "ok": boolean; "error": string };
