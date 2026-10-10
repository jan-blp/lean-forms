use serde::Deserialize;
use serde_json::Value;

#[derive(Clone, Debug, PartialEq, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase", deny_unknown_fields)]
pub enum Ty {
    Text,
    Boolean,
    Natural,
    Choice { options: Vec<String> },
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
pub enum Widget {
    TextInput,
    Checkbox,
    NaturalInput,
    Select,
}
impl Widget {
    fn matches(self, ty: &Ty) -> bool {
        match self {
            Self::TextInput => *ty == Ty::Text,
            Self::Checkbox => *ty == Ty::Boolean,
            Self::NaturalInput => *ty == Ty::Natural,
            Self::Select => matches!(ty, Ty::Choice { .. }),
        }
    }
}
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase", deny_unknown_fields)]
pub enum Form {
    Field { label: String, widget: Widget },
    Group { label: String, children: Vec<Form> },
    VisibleWhen { condition: Expr, body: Box<Form> },
}
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Constraint {
    condition: Expr,
    #[serde(rename = "errorMessage")]
    error_message: String,
    #[serde(rename = "errorLocation")]
    error_location: Option<Vec<usize>>,
}
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Specification {
    version: u32,
    constraints: Vec<Constraint>,
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
        Ty::Choice { options } => {
            let unique: std::collections::HashSet<_> = options.iter().collect();
            unique.len() == options.len()
                && value.as_u64().is_some_and(|i| i < options.len() as u64)
        }
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
            Self::Field { widget, .. } if widget.matches(ty) => Ok(()),
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
            _ => Err("Widget does not match field type".into()),
        }
    }
    fn fields(
        &self,
        ty: &Ty,
        value: &Value,
        path: Vec<usize>,
        labels: Vec<String>,
        out: &mut Vec<Field>,
    ) {
        match self {
            Self::Field { label, widget } => {
                let mut labels = labels;
                labels.push(label.clone());
                out.push(Field {
                    label: labels.join("."),
                    path,
                    widget: *widget,
                    options: match ty {
                        Ty::Choice { options } => options.clone(),
                        _ => vec![],
                    },
                });
            }
            Self::Group { label, children } => {
                let mut labels = labels;
                labels.push(label.clone());
                let Ty::Group { children: types } = ty else {
                    unreachable!()
                };
                for (index, (child, ty)) in children.iter().zip(types).enumerate() {
                    let mut child_path = path.clone();
                    child_path.push(index);
                    child.fields(ty, value, child_path, labels.clone(), out);
                }
            }
            Self::VisibleWhen { condition, body } => {
                if condition.eval(value).as_bool().unwrap() {
                    body.fields(ty, value, path, labels, out);
                }
            }
        }
    }
}
pub struct Field {
    pub label: String,
    path: Vec<usize>,
    widget: Widget,
    options: Vec<String>,
}
pub struct Editor {
    pub text: String,
    pub error: Option<String>,
    pub choice: Option<usize>,
    pub options: Vec<String>,
}
pub struct Engine {
    spec: Specification,
    submitted: bool,
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
        if spec.version != 2 {
            return Err("Unsupported form specification version".into());
        }
        validate_value(&spec.schema, &spec.value)?;
        spec.form.validate(&spec.schema, &spec.schema)?;
        for constraint in &spec.constraints {
            if constraint.condition.ty(&spec.schema)? != Ty::Boolean {
                return Err("Validation constraint requires a boolean".into());
            }
            if let Some(path) = &constraint.error_location {
                Expr::Project { path: path.clone() }.ty(&spec.schema)?;
            }
        }
        Ok(Self {
            spec,
            submitted: false,
            selected: 0,
            editor: None,
        })
    }
    pub fn result(&self) -> String {
        if self.submitted {
            self.spec.value.to_string()
        } else {
            "null".into()
        }
    }
    pub fn errors(&self) -> Vec<String> {
        let fields = self.fields();
        self.spec
            .constraints
            .iter()
            .filter(|constraint| {
                !constraint
                    .condition
                    .eval(&self.spec.value)
                    .as_bool()
                    .unwrap()
            })
            .map(|constraint| {
                match constraint
                    .error_location
                    .as_ref()
                    .and_then(|path| fields.iter().find(|field| &field.path == path))
                {
                    Some(field) => format!(
                        "{}: {}",
                        field.label.rsplit('.').next().unwrap(),
                        constraint.error_message
                    ),
                    None => constraint.error_message.clone(),
                }
            })
            .collect()
    }
    pub fn fields(&self) -> Vec<Field> {
        let mut out = Vec::new();
        self.spec.form.fields(
            &self.spec.schema,
            &self.spec.value,
            vec![],
            vec![],
            &mut out,
        );
        out
    }
    pub fn shown(&self, field: &Field) -> String {
        let value = get(&self.spec.value, &field.path);
        match field.widget {
            Widget::Checkbox => if value.as_bool().unwrap() {
                "[x]"
            } else {
                "[ ]"
            }
            .into(),
            Widget::Select => field.options[value.as_u64().unwrap() as usize].clone(),
            _ => value.as_str().unwrap().to_owned(),
        }
    }
    pub fn step(&mut self, key: Key) -> bool {
        if matches!(key, Key::Quit) {
            return false;
        }
        let fields = self.fields();
        if let Some(editor) = &mut self.editor {
            if let Some(index) = &mut editor.choice {
                match key {
                    Key::Up | Key::Character('k') => *index = index.saturating_sub(1),
                    Key::Down | Key::Character('j') => {
                        *index = (*index + 1).min(editor.options.len() - 1)
                    }
                    Key::Enter => {
                        if let Some(field) = fields.get(self.selected) {
                            set(&mut self.spec.value, &field.path, Value::from(*index));
                        }
                        self.editor = None;
                    }
                    Key::Escape => self.editor = None,
                    _ => {}
                }
            } else {
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
                            let parsed = match field.widget {
                                Widget::TextInput => Some(Value::String(editor.text.clone())),
                                Widget::NaturalInput => natural(
                                    editor.text.trim_matches(|c: char| c.is_ascii_whitespace()),
                                )
                                .map(Value::String),
                                Widget::Checkbox | Widget::Select => unreachable!(),
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
            }
        } else {
            match key {
                Key::Escape | Key::Character('x') => return false,
                Key::Character('q') => {
                    if self.errors().is_empty() {
                        self.submitted = true;
                        return false;
                    }
                }
                Key::Up | Key::Character('k') => self.selected = self.selected.saturating_sub(1),
                Key::Down | Key::Character('j') => {
                    self.selected = (self.selected + 1).min(fields.len().saturating_sub(1))
                }
                Key::Enter | Key::Character('i' | ' ') => {
                    if let Some(field) = fields.get(self.selected) {
                        match field.widget {
                            Widget::Checkbox => {
                                let value = !get(&self.spec.value, &field.path).as_bool().unwrap();
                                set(&mut self.spec.value, &field.path, Value::Bool(value));
                            }
                            _ if !matches!(key, Key::Character(' ')) => {
                                self.editor = Some(Editor {
                                    text: self.shown(field),
                                    error: None,
                                    choice: if matches!(field.widget, Widget::Select) {
                                        Some(get(&self.spec.value, &field.path).as_u64().unwrap()
                                            as usize)
                                    } else {
                                        None
                                    },
                                    options: field.options.clone(),
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
