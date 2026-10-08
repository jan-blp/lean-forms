use serde::Deserialize;
use serde_json::Value;

#[derive(Clone, Debug, PartialEq, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase", deny_unknown_fields)]
pub enum Ty {
    Text,
    Boolean,
    Natural,
    Pair { left: Box<Ty>, right: Box<Ty> },
}
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase", deny_unknown_fields)]
pub enum Expr {
    Value {
        #[serde(rename = "type")]
        ty: Ty,
        value: Value,
    },
    Project {
        path: Vec<usize>,
    },
    Not {
        operand: Box<Expr>,
    },
    And {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    TextEquals {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    NatLe {
        left: Box<Expr>,
        right: Box<Expr>,
    },
}
#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum Control {
    Text,
    Checkbox,
    Natural,
}
impl Control {
    fn ty(self) -> Ty {
        match self {
            Self::Text => Ty::Text,
            Self::Checkbox => Ty::Boolean,
            Self::Natural => Ty::Natural,
        }
    }
}
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase", deny_unknown_fields)]
pub enum Form {
    Field {
        label: String,
        control: Control,
    },
    Group {
        label: String,
        left: Box<Form>,
        right: Box<Form>,
    },
    VisibleWhen {
        condition: Expr,
        body: Box<Form>,
    },
}
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Specification {
    version: u32,
    schema: Ty,
    form: Form,
    value: Value,
}
fn natural(text: &str) -> Option<String> {
    if text.is_empty() || !text.bytes().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let digits = text.trim_start_matches('0');
    Some(if digits.is_empty() { "0" } else { digits }.to_owned())
}
fn validate_value(ty: &Ty, value: &Value) -> Result<(), String> {
    let valid = match ty {
        Ty::Text => value.is_string(),
        Ty::Boolean => value.is_boolean(),
        Ty::Natural => value.as_str().and_then(natural).is_some(),
        Ty::Pair { left, right } => value.as_array().is_some_and(|v| {
            v.len() == 2
                && validate_value(left, &v[0]).is_ok()
                && validate_value(right, &v[1]).is_ok()
        }),
    };
    if valid {
        Ok(())
    } else {
        Err(format!("Value does not match {ty:?}"))
    }
}
impl Expr {
    fn ty(&self, root: &Ty) -> Result<Ty, String> {
        match self {
            Self::Value { ty, value } => {
                validate_value(ty, value)?;
                Ok(ty.clone())
            }
            Self::Project { path } => {
                let mut ty = root;
                for step in path {
                    ty = match (ty, step) {
                        (Ty::Pair { left, .. }, 0) => left,
                        (Ty::Pair { right, .. }, 1) => right,
                        _ => return Err("Invalid expression path".into()),
                    };
                }
                Ok(ty.clone())
            }
            Self::Not { operand } => {
                if operand.ty(root)? != Ty::Boolean {
                    return Err("not requires boolean".into());
                }
                Ok(Ty::Boolean)
            }
            Self::And { left, right }
            | Self::TextEquals { left, right }
            | Self::NatLe { left, right } => {
                let expected = match self {
                    Self::And { .. } => Ty::Boolean,
                    Self::TextEquals { .. } => Ty::Text,
                    _ => Ty::Natural,
                };
                if left.ty(root)? != expected || right.ty(root)? != expected {
                    return Err("Invalid predicate operands".into());
                }
                Ok(Ty::Boolean)
            }
        }
    }
    fn eval(&self, root: &Value) -> Value {
        match self {
            Self::Value { value, .. } => value.clone(),
            Self::Project { path } => get(root, path).clone(),
            Self::Not { operand } => Value::Bool(!operand.eval(root).as_bool().unwrap()),
            Self::And { left, right } => Value::Bool(
                left.eval(root).as_bool().unwrap() && right.eval(root).as_bool().unwrap(),
            ),
            Self::TextEquals { left, right } => Value::Bool(left.eval(root) == right.eval(root)),
            Self::NatLe { left, right } => {
                let l = natural(left.eval(root).as_str().unwrap()).unwrap();
                let r = natural(right.eval(root).as_str().unwrap()).unwrap();
                Value::Bool((l.len(), &l) <= (r.len(), &r))
            }
        }
    }
}
fn get<'a>(mut value: &'a Value, path: &[usize]) -> &'a Value {
    for step in path {
        value = &value[*step];
    }
    value
}
fn set(value: &mut Value, path: &[usize], replacement: Value) {
    if let Some((first, rest)) = path.split_first() {
        set(&mut value[*first], rest, replacement);
    } else {
        *value = replacement;
    }
}
impl Form {
    fn validate(&self, root: &Ty, ty: &Ty) -> Result<(), String> {
        match self {
            Self::Field { control, .. } if control.ty() == *ty => Ok(()),
            Self::Group { left, right, .. } => match ty {
                Ty::Pair { left: l, right: r } => {
                    left.validate(root, l)?;
                    right.validate(root, r)
                }
                _ => Err("Group requires pair schema".into()),
            },
            Self::VisibleWhen { condition, body } => {
                if condition.ty(root)? != Ty::Boolean {
                    return Err("Visibility requires boolean".into());
                }
                body.validate(root, ty)
            }
            _ => Err("Control does not match field type".into()),
        }
    }
    fn fields(&self, value: &Value, path: Vec<usize>, labels: Vec<String>, out: &mut Vec<Field>) {
        match self {
            Self::Field { label, control } => {
                let mut labels = labels;
                labels.push(label.clone());
                out.push(Field {
                    label: labels.join("."),
                    path,
                    control: *control,
                });
            }
            Self::Group { label, left, right } => {
                let mut labels = labels;
                labels.push(label.clone());
                let mut l = path.clone();
                l.push(0);
                let mut r = path;
                r.push(1);
                left.fields(value, l, labels.clone(), out);
                right.fields(value, r, labels, out);
            }
            Self::VisibleWhen { condition, body } => {
                if condition.eval(value).as_bool().unwrap() {
                    body.fields(value, path, labels, out);
                }
            }
        }
    }
}
pub struct Field {
    pub label: String,
    path: Vec<usize>,
    control: Control,
}
pub struct Editor {
    pub text: String,
    pub error: Option<String>,
}
pub struct Engine {
    spec: Specification,
    pub selected: usize,
    pub editor: Option<Editor>,
}
#[derive(Clone, Copy)]
pub enum Key {
    Up,
    Down,
    Enter,
    Escape,
    Backspace,
    Clear,
    Quit,
    Character(char),
}
impl Engine {
    pub fn parse(json: &str) -> Result<Self, String> {
        let spec: Specification = serde_json::from_str(json).map_err(|e| e.to_string())?;
        if spec.version != 1 {
            return Err("Unsupported form specification version".into());
        }
        validate_value(&spec.schema, &spec.value)?;
        spec.form.validate(&spec.schema, &spec.schema)?;
        Ok(Self {
            spec,
            selected: 0,
            editor: None,
        })
    }
    pub fn result(&self) -> String {
        self.spec.value.to_string()
    }
    pub fn fields(&self) -> Vec<Field> {
        let mut out = Vec::new();
        self.spec
            .form
            .fields(&self.spec.value, vec![], vec![], &mut out);
        out
    }
    pub fn shown(&self, field: &Field) -> String {
        let value = get(&self.spec.value, &field.path);
        match field.control {
            Control::Checkbox => if value.as_bool().unwrap() {
                "[x]"
            } else {
                "[ ]"
            }
            .into(),
            _ => value.as_str().unwrap().to_owned(),
        }
    }
    pub fn step(&mut self, key: Key) -> bool {
        if matches!(key, Key::Quit) {
            return false;
        }
        let fields = self.fields();
        if let Some(editor) = &mut self.editor {
            match key {
                Key::Escape => self.editor = None,
                Key::Clear => {
                    editor.text.clear();
                    editor.error = None;
                }
                Key::Backspace => {
                    editor.text.pop();
                    editor.error = None;
                }
                Key::Character(c) => {
                    editor.text.push(c);
                    editor.error = None;
                }
                Key::Enter => {
                    if let Some(field) = fields.get(self.selected) {
                        let parsed = match field.control {
                            Control::Text => Some(Value::String(editor.text.clone())),
                            Control::Natural => {
                                natural(editor.text.trim_matches(|c: char| c.is_ascii_whitespace()))
                                    .map(Value::String)
                            }
                            Control::Checkbox => unreachable!(),
                        };
                        if let Some(value) = parsed {
                            set(&mut self.spec.value, &field.path, value);
                            self.editor = None;
                        } else {
                            editor.error = Some("Enter a non-negative whole number.".into());
                        }
                    }
                }
                _ => {}
            }
        } else {
            match key {
                Key::Escape | Key::Character('q') => return false,
                Key::Up | Key::Character('k') => self.selected = self.selected.saturating_sub(1),
                Key::Down | Key::Character('j') => {
                    self.selected = (self.selected + 1).min(fields.len().saturating_sub(1))
                }
                Key::Enter | Key::Character('i' | ' ') => {
                    if let Some(field) = fields.get(self.selected) {
                        match field.control {
                            Control::Checkbox => {
                                let value = !get(&self.spec.value, &field.path).as_bool().unwrap();
                                set(&mut self.spec.value, &field.path, Value::Bool(value));
                            }
                            _ if !matches!(key, Key::Character(' ')) => {
                                self.editor = Some(Editor {
                                    text: self.shown(field),
                                    error: None,
                                })
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
        self.selected = self.selected.min(self.fields().len().saturating_sub(1));
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    fn person() -> Engine {
        Engine::parse(include_str!("../tests/person.json")).unwrap()
    }
    fn keys(engine: &mut Engine, keys: &[Key]) {
        for key in keys {
            assert!(engine.step(*key));
        }
    }
    fn text(engine: &mut Engine, text: &str) {
        for c in text.chars() {
            assert!(engine.step(Key::Character(c)));
        }
    }
    #[test]
    fn edits_validate_and_hidden_values_survive() {
        let mut e = person();
        assert_eq!(e.fields().len(), 2);
        keys(
            &mut e,
            &[
                Key::Up,
                Key::Down,
                Key::Character(' '),
                Key::Down,
                Key::Down,
                Key::Down,
                Key::Enter,
                Key::Clear,
            ],
        );
        assert_eq!(e.fields().len(), 4);
        assert_eq!(e.fields()[3].label, "Person.Newsletter.Address.Number");
        for invalid in ["", "-1", "1.5", "abc", "+2"] {
            keys(&mut e, &[Key::Clear]);
            text(&mut e, invalid);
            keys(&mut e, &[Key::Enter]);
            assert_eq!(
                e.editor.as_ref().unwrap().error.as_deref(),
                Some("Enter a non-negative whole number.")
            );
            assert_eq!(e.spec.value[1][1][1], "12");
        }
        keys(&mut e, &[Key::Clear]);
        text(&mut e, " 0042 ");
        keys(&mut e, &[Key::Enter, Key::Up, Key::Up, Key::Character(' ')]);
        assert_eq!(e.fields().len(), 2);
        assert_eq!(e.spec.value[1][1][1], "42");
        keys(&mut e, &[Key::Character(' ')]);
        assert_eq!(e.fields().len(), 4);
        assert_eq!(
            serde_json::from_str::<Value>(&e.result()).unwrap(),
            json!(["Ada", [true, ["Lambda Lane", "42"]]])
        );
    }
    #[test]
    fn cancellation_unicode_empty_text_and_quit() {
        let mut e = person();
        keys(&mut e, &[Key::Enter, Key::Clear]);
        text(&mut e, "changed");
        keys(&mut e, &[Key::Escape]);
        assert_eq!(e.spec.value[0], "Ada");
        keys(&mut e, &[Key::Enter, Key::Clear]);
        text(&mut e, "é");
        keys(&mut e, &[Key::Backspace]);
        text(&mut e, "qjki\0界");
        keys(&mut e, &[Key::Enter]);
        assert_eq!(e.spec.value[0], "qjki\0界");
        keys(&mut e, &[Key::Enter, Key::Clear, Key::Enter]);
        assert_eq!(e.spec.value[0], "");
        keys(&mut e, &[Key::Enter]);
        text(&mut e, "discarded");
        assert!(!e.step(Key::Quit));
        assert_eq!(e.spec.value[0], "");
        let mut e = person();
        assert!(!e.step(Key::Character('q')));
    }
    #[test]
    fn all_predicates_and_unbounded_naturals() {
        let root = Ty::Pair {
            left: Box::new(Ty::Text),
            right: Box::new(Ty::Natural),
        };
        let expr: Expr = serde_json::from_value(json!({"kind":"and", "left": {"kind":"textEquals", "left":{"kind":"project","path":[0]},"right":{"kind":"value","type":{"kind":"text"},"value":"Ada"}},"right":{"kind":"not","operand":{"kind":"natLe","left":{"kind":"project","path":[1]},"right":{"kind":"value","type":{"kind":"natural"},"value":"9"}}}})).unwrap();
        assert_eq!(expr.ty(&root).unwrap(), Ty::Boolean);
        assert_eq!(
            expr.eval(&json!([
                "Ada",
                "10000000000000000000000000000000000000000000000"
            ])),
            true
        );
        assert_eq!(expr.eval(&json!(["Ada", "0009"])), false);
        assert_eq!(expr.eval(&json!(["Bob", "10"])), false);
        let mut e = person();
        keys(
            &mut e,
            &[
                Key::Down,
                Key::Enter,
                Key::Down,
                Key::Down,
                Key::Enter,
                Key::Clear,
            ],
        );
        let big = "12345678901234567890123456789012345678901234567890";
        text(&mut e, big);
        keys(&mut e, &[Key::Enter]);
        assert_eq!(e.spec.value[1][1][1], big);
    }
    #[test]
    fn invalid_specifications_are_rejected_before_rendering() {
        let source: Value = serde_json::from_str(include_str!("../tests/person.json")).unwrap();
        for (path, replacement) in [
            ("/version", json!(2)),
            ("/value/1/1/1", json!(-1)),
            ("/value/1/1", json!(["street"])),
            ("/form/left/control", json!("checkbox")),
            ("/form/right/right/condition/path", json!([2])),
            ("/form/right/right/condition/path", json!([0])),
        ] {
            let mut v = source.clone();
            *v.pointer_mut(path).unwrap() = replacement;
            assert!(Engine::parse(&v.to_string()).is_err(), "{path}");
        }
        assert!(Engine::parse("{}").is_err());
        let mut v = source;
        v["extra"] = json!(true);
        assert!(Engine::parse(&v.to_string()).is_err());
    }
    #[test]
    fn hidden_root_and_visibility_changed_by_edit() {
        let spec = json!({"version":1,"schema":{"kind":"text"},"value":"show","form":{"kind":"visibleWhen","condition":{"kind":"textEquals","left":{"kind":"project","path":[]},"right":{"kind":"value","type":{"kind":"text"},"value":"show"}},"body":{"kind":"field","label":"Name","control":"text"}}});
        let mut e = Engine::parse(&spec.to_string()).unwrap();
        keys(&mut e, &[Key::Enter, Key::Clear, Key::Enter]);
        assert!(e.fields().is_empty());
        assert_eq!(e.selected, 0);
        keys(
            &mut e,
            &[Key::Up, Key::Down, Key::Enter, Key::Character(' ')],
        );
        assert_eq!(e.result(), "\"\"");
    }
}
