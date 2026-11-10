// Generated from Lean. Run npm --prefix web run generate.
import type * as FormsReact from "../../FormsReact.js";

export type Request = { "open": { "start": FormStart } } | { "send": { "handle": string; "request": Command } } | { "dispose": { "handle": string } };
export type FormStart = { "form": string; "fingerprint": string; "value": unknown };
export type Command = { "event": { "message": Event } } | { "apply": { "key": string; "argument": unknown } } | "reset" | "validate" | "inspect" | { "serverError": { "status": number; "body": string } };
export type Event = { "apply": { "key": string; "argument": unknown } } | "submit" | "reset" | { "submitted": { "outcome": HttpOutcome } } | { "fetched": { "id": string; "outcome": HttpOutcome } };
export type HttpOutcome = { "response": { "status": number; "body": string } } | { "unreachable": { "message": string } };
export type Success = { "ok": boolean; "value": Response };
export type Response = { "opened": { "handle": string; "snapshot": Snapshot } } | { "updated": { "snapshot": Snapshot } } | "disposed";
export type Snapshot = { "title": string; "view": FormsReact.Component; "rejection": string | null; "draftFields": string[]; "effects": Effect[]; "summary": string; "submissionBlocked": boolean; "controls": unknown[]; "submission": unknown; "errors": unknown[] };
export type Effect = { "submit": { "request": HttpEffect } } | { "fetch": { "id": string; "request": HttpEffect } };
export type HttpEffect = { "url": string; "method": HttpMethod; "headers": HttpHeaders; "body": string | null };
export type HttpMethod = "GET" | "POST";
export type HttpHeaders = { "Content-Type": string };
export type Failure = { "ok": boolean; "error": string };
