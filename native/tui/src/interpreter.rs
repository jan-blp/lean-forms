use serde::Deserialize;
use serde_json::Value;

#[derive(Clone, Debug, PartialEq, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase", deny_unknown_fields)]
pub enum Ty {
    Text,
    Boolean,
    Natural,
    Group { children: Vec<Ty> },
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
    And {
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
    Field { label: String, control: Control },
    Group { label: String, children: Vec<Form> },
    VisibleWhen { condition: Expr, body: Box<Form> },
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
        Ty::Group { children } => value.as_array().is_some_and(|v| {
            v.len() == children.len()
                && children
                    .iter()
                    .zip(v)
                    .all(|(ty, value)| validate_value(ty, value).is_ok())
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
                        (Ty::Group { children }, index) => {
                            children.get(*index).ok_or("Invalid expression path")?
                        }
                        _ => return Err("Invalid expression path".into()),
                    };
                }
                Ok(ty.clone())
            }
            Self::And { left, right } | Self::NatLe { left, right } => {
                let expected = match self {
                    Self::And { .. } => Ty::Boolean,
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
            Self::And { left, right } => Value::Bool(
                left.eval(root).as_bool().unwrap() && right.eval(root).as_bool().unwrap(),
            ),
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
            Self::Group { children, .. } => match ty {
                Ty::Group { children: types } if children.len() == types.len() => {
                    for (child, ty) in children.iter().zip(types) {
                        child.validate(root, ty)?;
                    }
                    Ok(())
                }
                _ => Err("Group children must match schema".into()),
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
            Self::Group { label, children } => {
                let mut labels = labels;
                labels.push(label.clone());
                for (index, child) in children.iter().enumerate() {
                    let mut child_path = path.clone();
                    child_path.push(index);
                    child.fields(value, child_path, labels.clone(), out);
                }
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
mod tests;
