// Generated from Lean. Run npm --prefix web run generate.
export type Component = { "textField": TextField } | { "naturalField": NaturalField } | { "checkbox": Checkbox } | { "choice": Choice } | { "output": Output } | { "button": Button } | { "group": Group } | { "page": Page };
export type TextField = { "name": string; "label": string; "value": string; "disabled": boolean; "error": string | null; "onCommit": Action };
export type Action = { "apply": { "name": string } } | "submit" | "reset";
export type NaturalField = { "name": string; "label": string; "value": string; "disabled": boolean; "error": string | null; "onCommit": Action };
export type Checkbox = { "name": string; "label": string; "checked": boolean; "disabled": boolean; "error": string | null; "onChange": Action };
export type Choice = { "name": string; "label": string; "value": string; "options": ChoiceOption[]; "disabled": boolean; "error": string | null; "onChange": Action };
export type ChoiceOption = { "value": string; "label": string };
export type Output = { "label": string; "value": string };
export type Button = { "label": string; "variant": ButtonVariant; "disabled": boolean; "onClick": Action };
export type ButtonVariant = "primary" | "secondary";
export type Group = { "label": string | null; "children": Component[]; "error": string | null };
export type Page = { "title": string; "busy": boolean; "body": Component[]; "toolbar": Component[]; "notice": Notice; "result": string | null };
export type Notice = { "info": { "message": string } } | { "error": { "message": string } };
