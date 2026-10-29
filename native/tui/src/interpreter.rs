use chrono::{Datelike, Days, Months, NaiveDate};
use num_bigint::BigUint;
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
    List { element: Box<Ty> },
    Sum { constructors: Vec<NamedType> },
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
    #[serde(skip)]
    Payload(String),
}

fn matches_names<T>(values: &BTreeMap<String, T>, types: &[NamedType]) -> bool {
    values.len() == types.len() && types.iter().all(|ty| values.contains_key(&ty.name))
}

impl Ty {
    fn validate(&self) -> Result<(), String> {
        match self {
            Self::Record { fields }
            | Self::Sum {
                constructors: fields,
            } => {
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
            Self::Enum { options } => {
                let unique: std::collections::HashSet<_> = options.iter().collect();
                if unique.len() != options.len() {
                    return Err("Enum names must be unique".into());
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
    All {
        items: Box<Expr>,
        predicate: Box<Expr>,
    },
    Cases {
        #[serde(rename = "type")]
        ty: Ty,
        subject: Box<Expr>,
        branches: BTreeMap<String, Expr>,
    },
    Sum {
        items: Box<Expr>,
        expression: Box<Expr>,
    },
    Filter {
        items: Box<Expr>,
        predicate: Box<Expr>,
    },
    SortBy {
        items: Box<Expr>,
        key: Box<Expr>,
        descending: bool,
    },
    Search {
        items: Box<Expr>,
        key: Box<Expr>,
        query: Box<Expr>,
    },
    SortNatBy {
        items: Box<Expr>,
        key: Box<Expr>,
        descending: bool,
    },
    Length {
        items: Box<Expr>,
    },
    EnumCases {
        #[serde(rename = "type")]
        ty: Ty,
        subject: Box<Expr>,
        branches: Vec<Expr>,
    },
    EnumEq {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    EnumLabel {
        subject: Box<Expr>,
        options: Vec<String>,
    },
    IfThenElse {
        condition: Box<Expr>,
        #[serde(rename = "whenTrue")]
        when_true: Box<Expr>,
        #[serde(rename = "whenFalse")]
        when_false: Box<Expr>,
    },
    NatToText {
        operand: Box<Expr>,
    },
    TextAppend {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    NatMul {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Not {
        operand: Box<Expr>,
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
    #[serde(skip)]
    Computed,
    #[serde(skip)]
    Add,
    #[serde(skip)]
    Constructor,
    #[serde(skip)]
    Remove,
}
impl Widget {
    fn matches(self, ty: &Ty) -> bool {
        match self {
            Self::Computed | Self::Add | Self::Remove | Self::Constructor => false,
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
pub enum Component {
    Stack {
        #[serde(default)]
        label: Option<String>,
        children: Vec<Component>,
    },
    AppendItemButton {
        label: String,
        path: Vec<Step>,
        value: Expr,
    },
    Text {
        expression: Expr,
    },
    Table {
        rows: Expr,
        columns: Vec<Column>,
    },
    Field {
        path: Vec<Step>,
        schema: Ty,
        label: String,
        widget: Widget,
    },
    List {
        path: Vec<Step>,
        schema: Ty,
        label: String,
        item: Box<Component>,
        #[serde(rename = "defaultItem")]
        default_item: Value,
    },
    Sum {
        path: Vec<Step>,
        schema: Ty,
        label: String,
        branches: BTreeMap<String, Component>,
        defaults: BTreeMap<String, Value>,
    },
    DisabledWhen {
        condition: Expr,
        body: Box<Component>,
    },
    Computed {
        label: String,
        #[serde(rename = "type")]
        ty: Ty,
        expression: Expr,
    },
    VisibleWhen {
        condition: Expr,
        body: Box<Component>,
    },
}
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Column {
    label: String,
    expression: Expr,
}

#[derive(Debug, PartialEq)]
pub struct ReportTable {
    pub columns: Vec<String>,
    pub rows: Vec<Vec<String>>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Constraint {
    condition: Expr,
    #[serde(rename = "errorMessage")]
    error_message: String,
    #[serde(rename = "errorLocation")]
    error_location: Option<Vec<Step>>,
}
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Specification {
    version: u32,
    constraints: Vec<Constraint>,
    schema: Ty,
    form: Component,
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
        Ty::Sum { constructors } => value.as_object().is_some_and(|object| {
            object.len() == 2
                && object
                    .get("tag")
                    .and_then(Value::as_str)
                    .and_then(|tag| {
                        constructors
                            .iter()
                            .find(|constructor| constructor.name == tag)
                    })
                    .zip(object.get("value"))
                    .is_some_and(|(ty, payload)| validate_value(&ty.ty, payload).is_ok())
        }),
        Ty::List { element } => value
            .as_array()
            .is_some_and(|items| items.iter().all(|v| validate_value(element, v).is_ok())),
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
fn show_value(ty: &Ty, value: &Value) -> String {
    match ty {
        Ty::Text | Ty::Natural | Ty::Date => value.as_str().unwrap().to_owned(),
        Ty::Boolean => value.as_bool().unwrap().to_string(),
        Ty::Enum { options } => options[value.as_u64().unwrap() as usize].clone(),
        Ty::List { element } => format!(
            "[{}]",
            value
                .as_array()
                .unwrap()
                .iter()
                .map(|item| show_value(element, item))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Ty::Record { fields } => format!(
            "{{{}}}",
            fields
                .iter()
                .map(|field| format!(
                    "{}: {}",
                    field.name,
                    show_value(&field.ty, &value[&field.name])
                ))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Ty::Sum { constructors } => {
            let tag = value["tag"].as_str().unwrap();
            let constructor = constructors
                .iter()
                .find(|constructor| constructor.name == tag)
                .unwrap();
            format!("{}: {}", tag, show_value(&constructor.ty, &value["value"]))
        }
    }
}

impl Expr {
    fn ty(&self, input: &Ty) -> Result<Ty, String> {
        match self {
            Self::Value { ty, value } => {
                ty.validate()?;
                validate_value(ty, value)?;
                Ok(ty.clone())
            }
            Self::Project { path } => {
                let mut ty = input;
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
            Self::Cases {
                ty,
                subject,
                branches,
            } => {
                let Ty::Sum { constructors } = subject.ty(input)? else {
                    return Err("cases requires a sum".into());
                };
                ty.validate()?;
                if !matches_names(branches, &constructors) {
                    return Err("cases requires one branch per constructor".into());
                }
                for constructor in &constructors {
                    if branches[&constructor.name].ty(&constructor.ty)? != *ty {
                        return Err("cases branches must match the result type".into());
                    }
                }
                Ok(ty.clone())
            }
            Self::All { items, predicate } => {
                let Ty::List { element } = items.ty(input)? else {
                    return Err("all requires a list".into());
                };
                if predicate.ty(&element)? != Ty::Boolean {
                    return Err("all requires a boolean predicate".into());
                }
                Ok(Ty::Boolean)
            }
            Self::Sum { items, expression } => {
                let Ty::List { element } = items.ty(input)? else {
                    return Err("sum requires a list".into());
                };
                if expression.ty(&element)? != Ty::Natural {
                    return Err("sum requires natural values".into());
                }
                Ok(Ty::Natural)
            }
            Self::Filter { items, predicate } => {
                let Ty::List { element } = items.ty(input)? else {
                    return Err("filter requires a list".into());
                };
                if predicate.ty(&element)? != Ty::Boolean {
                    return Err("filter requires a boolean predicate".into());
                }
                Ok(Ty::List { element })
            }
            Self::SortBy { items, key, .. } => {
                let Ty::List { element } = items.ty(input)? else {
                    return Err("sortBy requires a list".into());
                };
                if key.ty(&element)? != Ty::Text {
                    return Err("sortBy requires a text key".into());
                }
                Ok(Ty::List { element })
            }
            Self::Search { items, key, query } => {
                let Ty::List { element } = items.ty(input)? else {
                    return Err("search requires a list".into());
                };
                if key.ty(&element)? != Ty::Text || query.ty(input)? != Ty::Text {
                    return Err("search requires a text key and query".into());
                }
                Ok(Ty::List { element })
            }
            Self::SortNatBy { items, key, .. } => {
                let Ty::List { element } = items.ty(input)? else {
                    return Err("sortNatBy requires a list".into());
                };
                if key.ty(&element)? != Ty::Natural {
                    return Err("sortNatBy requires a natural key".into());
                }
                Ok(Ty::List { element })
            }
            Self::Length { items } => {
                if !matches!(items.ty(input)?, Ty::List { .. }) {
                    return Err("length requires a list".into());
                }
                Ok(Ty::Natural)
            }
            Self::EnumCases {
                ty,
                subject,
                branches,
            } => {
                let Ty::Enum { options } = subject.ty(input)? else {
                    return Err("enumCases requires an enum".into());
                };
                ty.validate()?;
                if branches.len() != options.len() {
                    return Err("enumCases requires one branch per option".into());
                }
                for branch in branches {
                    if branch.ty(input)? != *ty {
                        return Err("enumCases branches must match the result type".into());
                    }
                }
                Ok(ty.clone())
            }
            Self::EnumEq { left, right } => {
                let ty = left.ty(input)?;
                if !matches!(ty, Ty::Enum { .. }) || right.ty(input)? != ty {
                    return Err("enumEq requires matching enums".into());
                }
                Ok(Ty::Boolean)
            }
            Self::EnumLabel { subject, options } => {
                if subject.ty(input)?
                    != (Ty::Enum {
                        options: options.clone(),
                    })
                {
                    return Err("enumLabel options must match the enum".into());
                }
                Ok(Ty::Text)
            }
            Self::IfThenElse {
                condition,
                when_true,
                when_false,
            } => {
                let result = when_true.ty(input)?;
                if condition.ty(input)? != Ty::Boolean || when_false.ty(input)? != result {
                    return Err("ifThenElse requires a boolean and matching branches".into());
                }
                Ok(result)
            }
            Self::NatToText { operand } => {
                if operand.ty(input)? != Ty::Natural {
                    return Err("natToText requires a natural".into());
                }
                Ok(Ty::Text)
            }
            Self::TextAppend { left, right } => {
                if left.ty(input)? != Ty::Text || right.ty(input)? != Ty::Text {
                    return Err("textAppend requires text operands".into());
                }
                Ok(Ty::Text)
            }
            Self::NatMul { left, right } => {
                if left.ty(input)? != Ty::Natural || right.ty(input)? != Ty::Natural {
                    return Err("natMul requires natural operands".into());
                }
                Ok(Ty::Natural)
            }
            Self::Not { operand } => {
                if operand.ty(input)? != Ty::Boolean {
                    return Err("not requires boolean".into());
                }
                Ok(Ty::Boolean)
            }
            Self::And { left, right }
            | Self::NatLe { left, right }
            | Self::DateLe { left, right } => {
                let expected = match self {
                    Self::And { .. } => Ty::Boolean,
                    Self::DateLe { .. } => Ty::Date,
                    _ => Ty::Natural,
                };
                if left.ty(input)? != expected || right.ty(input)? != expected {
                    return Err("Invalid predicate operands".into());
                }
                Ok(Ty::Boolean)
            }
        }
    }
    // Expression types and values are validated before evaluation.
    fn eval_natural(&self, input: &Value) -> BigUint {
        self.eval(input).as_str().unwrap().parse().unwrap()
    }

    fn eval(&self, input: &Value) -> Value {
        match self {
            Self::Value { value, .. } => value.clone(),
            Self::Project { path } => get(input, path).clone(),
            Self::Cases {
                subject, branches, ..
            } => {
                let selected = subject.eval(input);
                let tag = selected["tag"].as_str().unwrap();
                branches[tag].eval(&selected["value"])
            }
            Self::All { items, predicate } => Value::Bool(
                items
                    .eval(input)
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|v| predicate.eval(v).as_bool().unwrap()),
            ),
            Self::Sum { items, expression } => Value::String(
                items
                    .eval(input)
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|item| expression.eval_natural(item))
                    .sum::<BigUint>()
                    .to_string(),
            ),
            Self::Filter { items, predicate } => Value::Array(
                items
                    .eval(input)
                    .as_array()
                    .unwrap()
                    .iter()
                    .filter(|item| predicate.eval(item).as_bool().unwrap())
                    .cloned()
                    .collect(),
            ),
            Self::SortBy {
                items,
                key,
                descending,
            } => {
                let mut rows = items.eval(input).as_array().unwrap().clone();
                rows.sort_by(|left, right| {
                    let left = key.eval(left);
                    let right = key.eval(right);
                    let order = left.as_str().unwrap().cmp(right.as_str().unwrap());
                    if *descending {
                        order.reverse()
                    } else {
                        order
                    }
                });
                Value::Array(rows)
            }
            Self::Search { items, key, query } => {
                let query = query.eval(input).as_str().unwrap().to_ascii_lowercase();
                Value::Array(items.eval(input).as_array().unwrap().iter()
                    .filter(|row| key.eval(row).as_str().unwrap().to_ascii_lowercase().contains(&query))
                    .cloned().collect())
            }
            Self::SortNatBy { items, key, descending } => {
                let mut rows = items.eval(input).as_array().unwrap().clone();
                rows.sort_by(|left, right| {
                    let order = key.eval_natural(left).cmp(&key.eval_natural(right));
                    if *descending { order.reverse() } else { order }
                });
                Value::Array(rows)
            }
            Self::Length { items } => {
                Value::String(items.eval(input).as_array().unwrap().len().to_string())
            }
            Self::EnumCases {
                subject, branches, ..
            } => branches[subject.eval(input).as_u64().unwrap() as usize].eval(input),
            Self::EnumEq { left, right } => Value::Bool(left.eval(input) == right.eval(input)),
            Self::EnumLabel { subject, options } => {
                Value::String(options[subject.eval(input).as_u64().unwrap() as usize].clone())
            }
            Self::IfThenElse {
                condition,
                when_true,
                when_false,
            } => {
                if condition.eval(input).as_bool().unwrap() {
                    when_true.eval(input)
                } else {
                    when_false.eval(input)
                }
            }
            Self::NatToText { operand } => Value::String(operand.eval_natural(input).to_string()),
            Self::TextAppend { left, right } => Value::String(format!(
                "{}{}",
                left.eval(input).as_str().unwrap(),
                right.eval(input).as_str().unwrap()
            )),
            Self::NatMul { left, right } => {
                Value::String((left.eval_natural(input) * right.eval_natural(input)).to_string())
            }
            Self::Not { operand } => Value::Bool(!operand.eval(input).as_bool().unwrap()),
            Self::And { left, right } => Value::Bool(
                left.eval(input).as_bool().unwrap() && right.eval(input).as_bool().unwrap(),
            ),
            Self::DateLe { left, right } => Value::Bool(
                date(left.eval(input).as_str().unwrap()).unwrap()
                    <= date(right.eval(input).as_str().unwrap()).unwrap(),
            ),
            Self::NatLe { left, right } => {
                Value::Bool(left.eval_natural(input) <= right.eval_natural(input))
            }
        }
    }
}
fn get<'a>(mut value: &'a Value, path: &[Step]) -> &'a Value {
    for step in path {
        value = match step {
            Step::Field(name) => &value[name],
            Step::Item(index) => &value[*index],
            Step::Payload(_) => &value["value"],
        };
    }
    value
}
fn set(value: &mut Value, path: &[Step], replacement: Value) {
    if let Some((first, rest)) = path.split_first() {
        let child = match first {
            Step::Field(name) => &mut value[name],
            Step::Item(index) => &mut value[*index],
            Step::Payload(_) => &mut value["value"],
        };
        set(child, rest, replacement);
    } else {
        *value = replacement;
    }
}

impl Component {
    fn validate(&self, context: &Ty) -> Result<(), String> {
        match self {
            Self::Field { path, schema, .. } | Self::List { path, schema, .. } | Self::Sum { path, schema, .. } => {
                schema.validate()?;
                if (Expr::Project { path: path.clone() }).ty(context)? != *schema {
                    return Err("Control schema must match its path".into());
                }
            }
            _ => {}
        }
        match self {
            Self::Stack { children, .. } => {
                for child in children {
                    child.validate(context)?;
                }
                Ok(())
            }
            Self::AppendItemButton { path, value, .. } => {
                let Ty::List { element } = (Expr::Project { path: path.clone() }).ty(context)? else {
                    return Err("appendItemButton requires a list target".into());
                };
                if value.ty(context)? != *element {
                    return Err("appendItemButton value must match list element type".into());
                }
                Ok(())
            }
            Self::Text { expression } => {
                if expression.ty(context)? != Ty::Text {
                    return Err("Text view requires text".into());
                }
                Ok(())
            }
            Self::Table { rows, columns } => {
                let Ty::List { element } = rows.ty(context)? else {
                    return Err("Table requires a list".into());
                };
                for column in columns {
                    if column.expression.ty(&element)? != Ty::Text {
                        return Err("Table cells require text".into());
                    }
                }
                Ok(())
            }
            Self::Sum {
                schema: ty, branches, defaults, ..
            } => {
                let Ty::Sum { constructors } = ty else {
                    return Err("Sum form requires sum schema".into());
                };
                if !matches_names(branches, constructors) || !matches_names(defaults, constructors)
                {
                    return Err("Sum branches and defaults must match schema".into());
                }
                for constructor in constructors {
                    validate_value(&constructor.ty, &defaults[&constructor.name])?;
                    branches[&constructor.name].validate(&constructor.ty)?;
                }
                Ok(())
            }
            Self::List {
                schema: ty, item, default_item, ..
            } => {
                let Ty::List { element } = ty else {
                    return Err("List form requires list schema".into());
                };
                validate_value(element, default_item)?;
                item.validate(element)
            }
            Self::Field { widget, schema, .. } if widget.matches(schema) => Ok(()),
            Self::Computed {
                ty: result,
                expression,
                ..
            } => {
                result.validate()?;
                if expression.ty(context)? != *result {
                    return Err("Computed expression must match its result type".into());
                }
                Ok(())
            }
            Self::DisabledWhen { condition, body } => {
                if condition.ty(context)? != Ty::Boolean {
                    return Err("Disabling requires boolean".into());
                }
                body.validate(context)
            }
            Self::VisibleWhen { condition, body } => {
                if condition.ty(context)? != Ty::Boolean {
                    return Err("Visibility requires boolean".into());
                }
                body.validate(context)
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
        tables: &mut Vec<ReportTable>,
    ) {
        match self {
            Self::Stack { children, label } => {
                let mut labels = labels;
                if let Some(label) = label {
                    if !(label == "Item" && labels.last().is_some_and(|parent| parent.starts_with("Item "))) {
                        labels.push(label.clone());
                    }
                }
                for child in children {
                    child.fields(ty, value, path.clone(), scope, labels.clone(), out, tables);
                }
            }
            Self::AppendItemButton { label, path: relative, value: expression } => out.push(Field {
                presentation: Presentation { add: true, ..Presentation::default() },
                title: label.clone(), section: labels.join(" › "), action: true,
                label: label.clone(), path: scope.iter().chain(relative).cloned().collect(),
                widget: Widget::Add, options: vec![],
                default_item: Some(expression.eval(get(value, scope))), computed_value: None,
            }),
            Self::Text { expression } => out.push(Field {
                presentation: Presentation {
                    computed: true,
                    text: true,
                    ..Presentation::default()
                },
                title: String::new(),
                section: labels.join(" › "),
                action: false,
                label: labels.join("."),
                path,
                widget: Widget::Computed,
                options: vec![],
                default_item: None,
                computed_value: Some(
                    expression
                        .eval(get(value, scope))
                        .as_str()
                        .unwrap()
                        .to_owned(),
                ),
            }),
            Self::Table { rows, columns } => {
                tables.push(ReportTable {
                    columns: columns.iter().map(|column| column.label.clone()).collect(),
                    rows: rows
                        .eval(get(value, scope))
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|row| {
                            columns
                                .iter()
                                .map(|column| {
                                    column.expression.eval(row).as_str().unwrap().to_owned()
                                })
                                .collect()
                        })
                        .collect(),
                });
            }
            Self::Sum {
                path: relative, schema: ty, label, branches, defaults,
            } => {
                let path: Vec<_> = scope.iter().chain(relative).cloned().collect();
                let Ty::Sum { constructors } = ty else {
                    unreachable!()
                };
                let tag = get(value, &path)["tag"].as_str().unwrap();
                let constructor = constructors
                    .iter()
                    .find(|constructor| constructor.name == tag)
                    .unwrap();
                let mut labels = labels;
                labels.push(label.clone());
                out.push(Field {
                    computed_value: None,
                    presentation: Presentation::default(),
                    title: label.clone(),
                    section: labels.join(" › "),
                    action: false,
                    label: labels.join("."),
                    path: path.clone(),
                    widget: Widget::Constructor,
                    options: constructors
                        .iter()
                        .map(|constructor| constructor.name.clone())
                        .collect(),
                    default_item: Some(Value::Array(
                        constructors
                            .iter()
                            .map(|constructor| defaults[&constructor.name].clone())
                            .collect(),
                    )),
                });
                let selector = out.len() - 1;
                out[selector].presentation.constructor = true;
                let section = labels.join(" › ");
                let mut payload_path = path;
                payload_path.push(Step::Payload(tag.to_owned()));
                labels.push(tag.to_owned());
                let payload_section = labels.join(" › ");
                branches[tag].fields(
                    &constructor.ty,
                    value,
                    payload_path.clone(),
                    &payload_path,
                    labels,
                    out,
                    tables,
                );
                // The selector names the payload. Keep deeper groups, but fold the
                // branch's outer group into this section instead of repeating it.
                let mut branch = &branches[tag];
                while let Self::VisibleWhen { body, .. } | Self::DisabledWhen { body, .. } = branch
                {
                    branch = body;
                }
                let prefix = if let Self::Stack { label: Some(label), .. } = branch {
                    format!("{payload_section} › {label}")
                } else {
                    payload_section
                };
                for field in &mut out[selector + 1..] {
                    field.presentation.depth += 1;
                    if field.section == prefix {
                        field.section = section.clone();
                    } else if let Some(suffix) = field.section.strip_prefix(&format!("{prefix} › "))
                    {
                        field.section = format!("{section} › {suffix}");
                    }
                }
                if out.len() == selector + 1 {
                    out[selector].presentation.note = Some(
                        if matches!(&constructor.ty, Ty::Record { fields } if fields.is_empty()) {
                            "No details required"
                        } else {
                            "No fields to edit"
                        },
                    );
                }
            }
            Self::List {
                path: relative, schema: ty, label, item, default_item,
            } => {
                let path: Vec<_> = scope.iter().chain(relative).cloned().collect();
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
                        tables,
                    );
                    let section = out
                        .last()
                        .filter(|field| field.path.starts_with(&item_path))
                        .map(|field| field.section.clone())
                        .unwrap_or_else(|| item_labels.join(" › "));
                    out.push(Field {
                        computed_value: None,
                        presentation: Presentation::default(),
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
                    computed_value: None,
                    presentation: Presentation {
                        add: true,
                        ..Presentation::default()
                    },
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
            Self::Computed {
                label,
                ty: result,
                expression,
            } => {
                let section = labels.join(" › ");
                let mut labels = labels;
                labels.push(label.clone());
                out.push(Field {
                    presentation: Presentation {
                        computed: true,
                        ..Presentation::default()
                    },
                    title: label.clone(),
                    section,
                    action: false,
                    label: labels.join("."),
                    path,
                    widget: Widget::Computed,
                    options: vec![],
                    default_item: None,
                    computed_value: Some(show_value(result, &expression.eval(get(value, scope)))),
                });
            }
            Self::Field { path: relative, schema: ty, label, widget } => {
                let path = scope.iter().chain(relative).cloned().collect();
                let mut labels = labels;
                let section = labels.join(" › ");
                labels.push(label.clone());
                out.push(Field {
                    computed_value: None,
                    presentation: Presentation {
                        choice: matches!(widget, Widget::Select),
                        ..Presentation::default()
                    },
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
            Self::DisabledWhen { condition, body } => {
                let start = out.len();
                body.fields(ty, value, path, scope, labels, out, tables);
                if condition.eval(get(value, scope)).as_bool().unwrap() {
                    for field in &mut out[start..] {
                        field.presentation.disabled = true;
                    }
                }
            }
            Self::VisibleWhen { condition, body } => {
                if condition.eval(get(value, scope)).as_bool().unwrap() {
                    body.fields(ty, value, path, scope, labels, out, tables);
                }
            }
        }
    }
}
#[derive(Clone, Copy, Default)]
pub struct Presentation {
    pub text: bool,
    pub computed: bool,
    pub add: bool,
    pub disabled: bool,
    pub constructor: bool,
    pub choice: bool,
    pub depth: usize,
    pub note: Option<&'static str>,
    pub invalid: bool,
}

pub struct Field {
    pub presentation: Presentation,
    pub label: String,
    pub title: String,
    pub section: String,
    pub action: bool,
    path: Vec<Step>,
    widget: Widget,
    options: Vec<String>,
    default_item: Option<Value>,
    computed_value: Option<String>,
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
    submitted: bool,
    constructor_drafts: std::collections::HashMap<(Vec<Step>, String), Value>,
    pub selected: usize,
    pub table_offset: usize,
    table_viewports: Vec<usize>,
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
        if spec.version != 4 {
            return Err("Unsupported component specification version".into());
        }
        spec.schema.validate()?;
        validate_value(&spec.schema, &spec.value)?;
        spec.form.validate(&spec.schema)?;
        for constraint in &spec.constraints {
            if constraint.condition.ty(&spec.schema)? != Ty::Boolean {
                return Err("Validation constraint requires a boolean".into());
            }
            if let Some(path) = &constraint.error_location {
                Expr::Project { path: path.clone() }.ty(&spec.schema)?;
            }
        }
        let mut engine = Self {
            spec,
            submitted: false,
            constructor_drafts: std::collections::HashMap::new(),
            selected: 0,
            table_offset: 0,
            table_viewports: vec![],
            editor: None,
        };
        engine.skip_text();
        Ok(engine)
    }
    pub fn set_table_viewports(&mut self, viewports: Vec<usize>) {
        self.table_viewports = viewports;
        self.clamp_table_offset();
    }

    fn maximum_table_offset(&self) -> usize {
        self.content().1.iter().enumerate().map(|(index, table)| {
            table.rows.len().saturating_sub(
                self.table_viewports.get(index).copied().unwrap_or(1).max(1))
        }).max().unwrap_or(0)
    }

    fn clamp_table_offset(&mut self) {
        self.table_offset = self.table_offset.min(self.maximum_table_offset());
    }

    fn skip_text(&mut self) {
        let fields = self.fields();
        self.selected = self.selected.min(fields.len().saturating_sub(1));
        if fields.get(self.selected).is_some_and(|field| field.presentation.text) {
            self.selected = (self.selected..fields.len())
                .find(|&index| !fields[index].presentation.text)
                .or_else(|| (0..self.selected).rev().find(|&index| !fields[index].presentation.text))
                .unwrap_or(0);
        }
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
                match constraint.error_location.as_ref().and_then(|path| {
                    fields
                        .iter()
                        .find(|field| !field.presentation.computed && &field.path == path)
                }) {
                    Some(field) if matches!(field.widget, Widget::Add) => format!(
                        "{}: {}",
                        field.label.trim_end_matches(".Add item"),
                        constraint.error_message
                    ),
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
    pub fn content(&self) -> (Vec<Field>, Vec<ReportTable>) {
        let mut out = Vec::new();
        let mut tables = Vec::new();
        self.spec.form.fields(
            &self.spec.schema,
            &self.spec.value,
            vec![],
            &[],
            vec![],
            &mut out,
            &mut tables,
        );
        for field in &mut out {
            if field.presentation.constructor {
                field.presentation.invalid = self.spec.constraints.iter().any(|constraint| {
                    constraint.error_location.as_ref() == Some(&field.path)
                        && !constraint
                            .condition
                            .eval(&self.spec.value)
                            .as_bool()
                            .unwrap()
                });
            }
        }
        (out, tables)
    }
    pub fn fields(&self) -> Vec<Field> {
        self.content().0
    }
    pub fn shown(&self, field: &Field) -> String {
        if let Some(value) = &field.computed_value {
            return value.clone();
        }
        let value = get(&self.spec.value, &field.path);
        match field.widget {
            Widget::Computed => unreachable!(),
            Widget::Add => "[+]".into(),
            Widget::Remove => "[-]".into(),
            Widget::Checkbox => if value.as_bool().unwrap() {
                "[x]"
            } else {
                "[ ]"
            }
            .into(),
            Widget::Constructor => value["tag"].as_str().unwrap().to_owned(),
            Widget::Select => field.options[value.as_u64().unwrap() as usize].clone(),
            _ => value.as_str().unwrap().to_owned(),
        }
    }
    pub fn step(&mut self, key: Key) -> bool {
        if matches!(key, Key::Quit) {
            return false;
        }
        if self.editor.is_none() && matches!(key, Key::PageUp | Key::PageDown) {
            let maximum = self.maximum_table_offset();
            let page_size = self.table_viewports.iter().copied().min().unwrap_or(1).max(1);
            self.table_offset = match key {
                Key::PageUp => self.table_offset.saturating_sub(page_size),
                _ => self.table_offset.saturating_add(page_size).min(maximum),
            };
            return true;
        }
        let fields = self.fields();
        if fields
            .get(self.selected)
            .is_some_and(|field| field.presentation.disabled || field.presentation.computed)
        {
            self.editor = None;
            if matches!(key, Key::Enter | Key::Character('i' | ' ')) {
                return true;
            }
        }
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
                            if matches!(field.widget, Widget::Constructor) {
                                let old = get(&self.spec.value, &field.path);
                                let old_tag = old["tag"].as_str().unwrap();
                                let tag = &field.options[*index];
                                if old_tag != tag {
                                    self.constructor_drafts.insert(
                                        (field.path.clone(), old_tag.to_owned()),
                                        old["value"].clone(),
                                    );
                                    let payload = self
                                        .constructor_drafts
                                        .remove(&(field.path.clone(), tag.clone()))
                                        .unwrap_or_else(|| {
                                            field.default_item.as_ref().unwrap()[*index].clone()
                                        });
                                    set(
                                        &mut self.spec.value,
                                        &field.path,
                                        serde_json::json!({"tag": tag, "value": payload}),
                                    );
                                }
                            } else {
                                set(&mut self.spec.value, &field.path, Value::from(*index));
                            }
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
                                Widget::Computed
                                | Widget::Checkbox
                                | Widget::Select
                                | Widget::Constructor
                                | Widget::Add
                                | Widget::Remove => unreachable!(),
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
                Key::Escape | Key::Character('x') => return false,
                Key::Character('q') => {
                    if self.errors().is_empty() {
                        self.submitted = true;
                        return false;
                    }
                }
                Key::Up | Key::Character('k') => {
                    if let Some(index) = (0..self.selected).rev().find(|&i| !fields[i].presentation.text) {
                        self.selected = index;
                    }
                },
                Key::Down | Key::Character('j') => {
                    if let Some(index) = (self.selected + 1..fields.len()).find(|&i| !fields[i].presentation.text) {
                        self.selected = index;
                    }
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
                                self.constructor_drafts =
                                    std::mem::take(&mut self.constructor_drafts)
                                        .into_iter()
                                        .filter_map(|((mut path, tag), draft)| {
                                            if path.starts_with(parent) && path.len() > parent.len()
                                            {
                                                let Step::Item(item_index) =
                                                    &mut path[parent.len()]
                                                else {
                                                    unreachable!()
                                                };
                                                if *item_index == *index {
                                                    return None;
                                                }
                                                if *item_index > *index {
                                                    *item_index -= 1;
                                                }
                                            }
                                            Some(((path, tag), draft))
                                        })
                                        .collect();
                                set(&mut self.spec.value, parent, Value::Array(items));
                            }
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
                                    choice: if matches!(field.widget, Widget::Constructor) {
                                        Some(
                                            field
                                                .options
                                                .iter()
                                                .position(|name| {
                                                    Some(name.as_str())
                                                        == get(&self.spec.value, &field.path)["tag"]
                                                            .as_str()
                                                })
                                                .unwrap(),
                                        )
                                    } else if matches!(field.widget, Widget::Select) {
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
        self.skip_text();
        self.clamp_table_offset();
        true
    }
}

#[cfg(test)]
mod tests;
