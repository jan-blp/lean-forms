use serde::Deserialize;
use serde_json::Value;
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase", deny_unknown_fields)]
pub enum Ty {
    Text,
    Boolean,
    Natural,
    Enum { options: Vec<String> },
    Record { fields: Vec<NamedType> },
    List { element: Box<Ty> },
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
    #[serde(skip)]
    Item(usize),
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
            Self::List { element } => element.validate()?,
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
    All {
        items: Box<Expr>,
        predicate: Box<Expr>,
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
    #[serde(skip)]
    Add,
    #[serde(skip)]
    Remove,
}
impl Widget {
    fn matches(self, ty: &Ty) -> bool {
        match self {
            Self::Add | Self::Remove => false,
            Self::TextInput => *ty == Ty::Text,
            Self::Checkbox => *ty == Ty::Boolean,
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
    List {
        label: String,
        item: Box<Form>,
        #[serde(rename = "defaultItem")]
        default_item: Value,
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
        Ty::List { element } => value
            .as_array()
            .is_some_and(|items| items.iter().all(|v| validate_value(element, v).is_ok())),
        Ty::Text => value.is_string(),
        Ty::Boolean => value.is_boolean(),
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
            Self::All { items, predicate } => {
                let Ty::List { element } = items.ty(root)? else {
                    return Err("all requires a list".into());
                };
                if predicate.ty(&element)? != Ty::Boolean {
                    return Err("all requires a boolean predicate".into());
                }
                Ok(Ty::Boolean)
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
            Self::All { items, predicate } => Value::Bool(
                items
                    .eval(root)
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|v| predicate.eval(v).as_bool().unwrap()),
            ),
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
fn get<'a>(mut value: &'a Value, path: &[Step]) -> &'a Value {
    for step in path {
        value = match step {
            Step::Field(name) => &value[name],
            Step::Item(index) => &value[*index],
        };
    }
    value
}
fn set(value: &mut Value, path: &[Step], replacement: Value) {
    if let Some((first, rest)) = path.split_first() {
        let child = match first {
            Step::Field(name) => &mut value[name],
            Step::Item(index) => &mut value[*index],
        };
        set(child, rest, replacement);
    } else {
        *value = replacement;
    }
}
impl Form {
    fn validate(&self, root: &Ty, ty: &Ty) -> Result<(), String> {
        match self {
            Self::List {
                item, default_item, ..
            } => {
                let Ty::List { element } = ty else {
                    return Err("List form requires list schema".into());
                };
                validate_value(element, default_item)?;
                item.validate(element, element)
            }
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
        scope: &[Step],
        labels: Vec<String>,
        out: &mut Vec<Field>,
    ) {
        match self {
            Self::List {
                label,
                item,
                default_item,
            } => {
                let Ty::List { element } = ty else {
                    unreachable!()
                };
                let mut labels = labels;
                labels.push(label.clone());
                for (index, _) in get(value, &path).as_array().unwrap().iter().enumerate() {
                    let mut item_path = path.clone();
                    item_path.push(Step::Item(index));
                    let mut item_labels = labels.clone();
                    item_labels.push(format!("Item {}", index + 1));
                    item.fields(
                        element,
                        value,
                        item_path.clone(),
                        &item_path,
                        item_labels.clone(),
                        out,
                    );
                    let section = out
                        .last()
                        .filter(|field| field.path.starts_with(&item_path))
                        .map(|field| field.section.clone())
                        .unwrap_or_else(|| item_labels.join(" › "));
                    out.push(Field {
                        title: "− Remove item".into(),
                        section,
                        action: true,
                        label: format!("{}.Remove", item_labels.join(".")),
                        path: item_path,
                        widget: Widget::Remove,
                        options: vec![],
                        default_item: None,
                    });
                }
                out.push(Field {
                    title: "+ Add item".into(),
                    section: labels.join(" › "),
                    action: true,
                    label: format!("{}.Add item", labels.join(".")),
                    path,
                    widget: Widget::Add,
                    options: vec![],
                    default_item: Some(default_item.clone()),
                });
            }
            Self::Field { label, widget } => {
                let mut labels = labels;
                let section = labels.join(" › ");
                labels.push(label.clone());
                out.push(Field {
                    title: label.clone(),
                    section,
                    action: false,
                    label: labels.join("."),
                    path,
                    widget: *widget,
                    default_item: None,
                    options: match ty {
                        Ty::Enum { options } => options.clone(),
                        _ => vec![],
                    },
                });
            }
            Self::Group { label, children } => {
                let mut labels = labels;
                if !(label == "Item"
                    && labels
                        .last()
                        .is_some_and(|parent| parent.starts_with("Item ")))
                {
                    labels.push(label.clone());
                }
                let Ty::Record { fields } = ty else {
                    unreachable!()
                };
                for field in fields {
                    let mut child_path = path.clone();
                    child_path.push(Step::Field(field.name.clone()));
                    children[&field.name].fields(
                        &field.ty,
                        value,
                        child_path,
                        scope,
                        labels.clone(),
                        out,
                    );
                }
            }
            Self::VisibleWhen { condition, body } => {
                if condition.eval(get(value, scope)).as_bool().unwrap() {
                    body.fields(ty, value, path, scope, labels, out);
                }
            }
        }
    }
}
pub struct Field {
    pub label: String,
    pub title: String,
    pub section: String,
    pub action: bool,
    path: Vec<Step>,
    widget: Widget,
    options: Vec<String>,
    default_item: Option<Value>,
}
pub struct Editor {
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
            &[],
            vec![],
            &mut out,
        );
        out
    }
    pub fn shown(&self, field: &Field) -> String {
        let value = get(&self.spec.value, &field.path);
        match field.widget {
            Widget::Add => "[+]".into(),
            Widget::Remove => "[-]".into(),
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
                                Widget::Checkbox
                                | Widget::Select
                                | Widget::Add
                                | Widget::Remove => unreachable!(),
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
                Key::Escape | Key::Character('q') => return false,
                Key::Up | Key::Character('k') => self.selected = self.selected.saturating_sub(1),
                Key::Down | Key::Character('j') => {
                    self.selected = (self.selected + 1).min(fields.len().saturating_sub(1))
                }
                Key::Enter | Key::Character('i' | ' ') => {
                    if let Some(field) = fields.get(self.selected) {
                        match field.widget {
                            Widget::Add => {
                                let mut items = get(&self.spec.value, &field.path)
                                    .as_array()
                                    .unwrap()
                                    .clone();
                                items.push(field.default_item.clone().unwrap());
                                set(&mut self.spec.value, &field.path, Value::Array(items));
                            }
                            Widget::Remove => {
                                let (Step::Item(index), parent) = field.path.split_last().unwrap()
                                else {
                                    unreachable!()
                                };
                                let mut items =
                                    get(&self.spec.value, parent).as_array().unwrap().clone();
                                items.remove(*index);
                                set(&mut self.spec.value, parent, Value::Array(items));
                            }
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
