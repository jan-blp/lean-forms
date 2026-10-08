use chrono::{Datelike, Days, Months, NaiveDate};
use serde::Deserialize;
use serde_json::Value;
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase", deny_unknown_fields)]
pub enum Ty {
    Text,
    Boolean,
    Natural,
    Date,
    Enum { options: Vec<String> },
    Record { fields: Vec<NamedType> },
}
#[derive(Clone, Debug, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NamedType {
    name: String,
    #[serde(rename = "type")]
    ty: Ty,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash, Deserialize)]
#[serde(untagged)]
pub enum Step {
    Field(String),
}
fn matches_names<T>(values: &BTreeMap<String, T>, types: &[NamedType]) -> bool {
    values.len() == types.len() && types.iter().all(|ty| values.contains_key(&ty.name))
}
impl Ty {
    fn validate(&self) -> Result<(), String> {
        match self {
            Self::Record { fields } => {
                let unique: std::collections::HashSet<_> =
                    fields.iter().map(|field| &field.name).collect();
                if unique.len() != fields.len() {
                    return Err("Schema names must be unique".into());
                }
                for field in fields {
                    field.ty.validate()?;
                }
            }
            _ => {}
        }
        Ok(())
    }
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
        path: Vec<Step>,
    },
    And {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    DateLe {
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
    DateInput,
    Select,
}
impl Widget {
    fn matches(self, ty: &Ty) -> bool {
        match self {
            Self::TextInput => *ty == Ty::Text,
            Self::Checkbox => *ty == Ty::Boolean,
            Self::DateInput => *ty == Ty::Date,
            Self::NaturalInput => *ty == Ty::Natural,
            Self::Select => matches!(ty, Ty::Enum { .. }),
        }
    }
}
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase", deny_unknown_fields)]
pub enum Form {
    Field {
        label: String,
        widget: Widget,
    },
    Group {
        label: String,
        children: BTreeMap<String, Form>,
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
fn date(text: &str) -> Option<NaiveDate> {
    let bytes = text.as_bytes();
    if bytes.len() != 10
        || bytes[4] != b'-'
        || bytes[7] != b'-'
        || !bytes
            .iter()
            .enumerate()
            .all(|(i, b)| i == 4 || i == 7 || b.is_ascii_digit())
    {
        return None;
    }
    let year = text[..4].parse().ok()?;
    if year == 0 {
        return None;
    }
    NaiveDate::from_ymd_opt(year, text[5..7].parse().ok()?, text[8..].parse().ok()?)
}

fn validate_value(ty: &Ty, value: &Value) -> Result<(), String> {
    let valid = match ty {
        Ty::Text => value.is_string(),
        Ty::Boolean => value.is_boolean(),
        Ty::Date => value.as_str().and_then(date).is_some(),
        Ty::Natural => value.as_str().and_then(natural).is_some(),
        Ty::Enum { options } => {
            let unique: std::collections::HashSet<_> = options.iter().collect();
            unique.len() == options.len()
                && value.as_u64().is_some_and(|i| i < options.len() as u64)
        }
        Ty::Record { fields } => value.as_object().is_some_and(|v| {
            v.len() == fields.len()
                && fields.iter().all(|field| {
                    v.get(&field.name)
                        .is_some_and(|value| validate_value(&field.ty, value).is_ok())
                })
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
                ty.validate()?;
                validate_value(ty, value)?;
                Ok(ty.clone())
            }
            Self::Project { path } => {
                let mut ty = root;
                for step in path {
                    ty = match (ty, step) {
                        (Ty::Record { fields }, Step::Field(name)) => {
                            &fields
                                .iter()
                                .find(|field| &field.name == name)
                                .ok_or("Invalid expression path")?
                                .ty
                        }
                        _ => return Err("Invalid expression path".into()),
                    };
                }
                Ok(ty.clone())
            }
            Self::And { left, right }
            | Self::NatLe { left, right }
            | Self::DateLe { left, right } => {
                let expected = match self {
                    Self::And { .. } => Ty::Boolean,
                    Self::DateLe { .. } => Ty::Date,
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
            Self::DateLe { left, right } => Value::Bool(
                date(left.eval(root).as_str().unwrap()).unwrap()
                    <= date(right.eval(root).as_str().unwrap()).unwrap(),
            ),
            Self::NatLe { left, right } => {
                let l = natural(left.eval(root).as_str().unwrap()).unwrap();
                let r = natural(right.eval(root).as_str().unwrap()).unwrap();
                Value::Bool((l.len(), &l) <= (r.len(), &r))
            }
        }
    }
}
fn get<'a>(mut value: &'a Value, path: &[Step]) -> &'a Value {
    for step in path {
        value = match step {
            Step::Field(name) => &value[name],
        };
    }
    value
}
fn set(value: &mut Value, path: &[Step], replacement: Value) {
    if let Some((first, rest)) = path.split_first() {
        let child = match first {
            Step::Field(name) => &mut value[name],
        };
        set(child, rest, replacement);
    } else {
        *value = replacement;
    }
}
impl Form {
    fn validate(&self, root: &Ty, ty: &Ty) -> Result<(), String> {
        match self {
            Self::Field { widget, .. } if widget.matches(ty) => Ok(()),
            Self::Group { children, .. } => match ty {
                Ty::Record { fields } if matches_names(children, fields) => {
                    for field in fields {
                        children[&field.name].validate(root, &field.ty)?;
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
        path: Vec<Step>,
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
                        Ty::Enum { options } => options.clone(),
                        _ => vec![],
                    },
                });
            }
            Self::Group { label, children } => {
                let mut labels = labels;
                labels.push(label.clone());
                let Ty::Record { fields } = ty else {
                    unreachable!()
                };
                for field in fields {
                    let mut child_path = path.clone();
                    child_path.push(Step::Field(field.name.clone()));
                    children[&field.name].fields(&field.ty, value, child_path, labels.clone(), out);
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
    path: Vec<Step>,
    widget: Widget,
    options: Vec<String>,
}
pub struct Editor {
    pub calendar: Option<NaiveDate>,
    pub date_input: bool,
    pub text: String,
    pub error: Option<String>,
    pub choice: Option<usize>,
    pub options: Vec<String>,
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
    Left,
    Right,
    PageUp,
    PageDown,
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
        spec.schema.validate()?;
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
            if let Some(current) = editor.calendar {
                if !editor.date_input {
                    match key {
                        Key::Character('i') | Key::Enter => editor.date_input = true,
                        Key::Escape => {
                            self.editor = None;
                            return true;
                        }
                        _ => {
                            let moved = match key {
                                Key::Left | Key::Character('h') => {
                                    current.checked_sub_days(Days::new(1))
                                }
                                Key::Right | Key::Character('l') => {
                                    current.checked_add_days(Days::new(1))
                                }
                                Key::Up | Key::Character('k') => {
                                    current.checked_sub_days(Days::new(7))
                                }
                                Key::Down | Key::Character('j') => {
                                    current.checked_add_days(Days::new(7))
                                }
                                Key::PageUp => current.checked_sub_months(Months::new(1)),
                                Key::PageDown => current.checked_add_months(Months::new(1)),
                                _ => None,
                            };
                            if let Some(next) =
                                moved.filter(|value| (1..=9999).contains(&value.year()))
                            {
                                editor.calendar = Some(next);
                                editor.text = next.to_string();
                                editor.error = None;
                            }
                        }
                    }
                    return true;
                }
                if matches!(key, Key::Escape) {
                    editor.date_input = false;
                    return true;
                }
            }

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
                                Widget::DateInput => date(
                                    editor.text.trim_matches(|c: char| c.is_ascii_whitespace()),
                                )
                                .map(|value| Value::String(value.to_string())),
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
                                editor.error = Some(
                                    if matches!(field.widget, Widget::DateInput) {
                                        "Enter a valid date: YYYY-MM-DD (0001–9999)."
                                    } else {
                                        "Enter a non-negative whole number."
                                    }
                                    .into(),
                                );
                            }
                        }
                    }
                    _ => {}
                }
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
                        match field.widget {
                            Widget::Checkbox => {
                                let value = !get(&self.spec.value, &field.path).as_bool().unwrap();
                                set(&mut self.spec.value, &field.path, Value::Bool(value));
                            }
                            _ if !matches!(key, Key::Character(' ')) => {
                                self.editor = Some(Editor {
                                    date_input: false,
                                    calendar: if matches!(field.widget, Widget::DateInput) {
                                        date(&self.shown(field))
                                    } else {
                                        None
                                    },
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
        if let Some(editor) = &mut self.editor {
            if editor.calendar.is_some() {
                if let Some(value) =
                    date(editor.text.trim_matches(|c: char| c.is_ascii_whitespace()))
                {
                    editor.calendar = Some(value);
                }
            }
        }
        self.selected = self.selected.min(self.fields().len().saturating_sub(1));
        true
    }
}

#[cfg(test)]
mod tests;
