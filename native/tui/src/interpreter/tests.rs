use super::*;
use serde_json::json;
fn person() -> Engine {
    Engine::parse(include_str!("../../tests/person.json")).unwrap()
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
    assert_eq!(e.fields().len(), 3);
    keys(
        &mut e,
        &[
            Key::Up,
            Key::Down,
            Key::Character(' '),
            Key::Down,
            Key::Down,
            Key::Enter,
            Key::Clear,
        ],
    );
    assert_eq!(e.fields().len(), 5);
    assert_eq!(e.fields()[3].label, "Person.Address.Number");
    for invalid in ["", "-1", "1.5", "abc", "+2"] {
        keys(&mut e, &[Key::Clear]);
        text(&mut e, invalid);
        keys(&mut e, &[Key::Enter]);
        assert_eq!(
            e.editor.as_ref().unwrap().error.as_deref(),
            Some("Enter a non-negative whole number.")
        );
        assert_eq!(e.spec.value["address"]["number"], "12");
    }
    keys(&mut e, &[Key::Clear]);
    text(&mut e, " 0042 ");
    keys(&mut e, &[Key::Enter, Key::Up, Key::Up, Key::Character(' ')]);
    assert_eq!(e.fields().len(), 3);
    assert_eq!(e.spec.value["address"]["number"], "42");
    keys(&mut e, &[Key::Character(' ')]);
    assert_eq!(e.fields().len(), 5);
    assert_eq!(
        serde_json::from_str::<Value>(&e.result()).unwrap(),
        json!({"name":"Ada","subscribed":true,"address":{"street":"Lambda Lane","number":"42","kind":0}})
    );
}
#[test]
fn cancellation_unicode_empty_text_and_quit() {
    let mut e = person();
    keys(&mut e, &[Key::Enter, Key::Clear]);
    text(&mut e, "changed");
    keys(&mut e, &[Key::Escape]);
    assert_eq!(e.spec.value["name"], "Ada");
    keys(&mut e, &[Key::Enter, Key::Clear]);
    text(&mut e, "é");
    keys(&mut e, &[Key::Backspace]);
    text(&mut e, "qjki\0界");
    keys(&mut e, &[Key::Enter]);
    assert_eq!(e.spec.value["name"], "qjki\0界");
    keys(&mut e, &[Key::Enter, Key::Clear, Key::Enter]);
    assert_eq!(e.spec.value["name"], "");
    keys(&mut e, &[Key::Enter]);
    text(&mut e, "discarded");
    assert!(!e.step(Key::Quit));
    assert_eq!(e.spec.value["name"], "");
    let mut e = person();
    assert!(!e.step(Key::Character('q')));
}
#[test]
fn all_predicates_and_unbounded_naturals() {
    let root = Ty::Record {
        fields: vec![
            NamedType {
                name: "name".into(),
                ty: Ty::Text,
            },
            NamedType {
                name: "number".into(),
                ty: Ty::Natural,
            },
        ],
    };
    let expr: Expr = serde_json::from_value(json!({"kind":"and", "left":{"kind":"value", "type":{"kind":"boolean"}, "value":true}, "right":{"kind":"natLe","left":{"kind":"value","type":{"kind":"natural"},"value":"10"},"right":{"kind":"project","path":["number"]}}})).unwrap();
    assert_eq!(expr.ty(&root).unwrap(), Ty::Boolean);
    assert_eq!(
        expr.eval(
            &json!({"name":"Ada","number":"10000000000000000000000000000000000000000000000"})
        ),
        true
    );
    assert_eq!(expr.eval(&json!({"name":"Ada","number":"0009"})), false);
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
    assert_eq!(e.spec.value["address"]["number"], big);
}
#[test]
fn choice_selection_cancellation_and_boundaries() {
    let mut e = person();
    keys(&mut e, &[Key::Down, Key::Down, Key::Enter]);
    assert_eq!(
        e.editor.as_ref().unwrap().options,
        ["Home", "Work", "Other"]
    );
    keys(&mut e, &[Key::Up, Key::Character('j'), Key::Escape]);
    assert_eq!(e.spec.value["address"]["kind"], 0);
    keys(&mut e, &[Key::Enter, Key::Down, Key::Enter]);
    assert_eq!(e.spec.value["address"]["kind"], 1);
    assert_eq!(e.shown(&e.fields()[2]), "Work");
    keys(
        &mut e,
        &[
            Key::Enter,
            Key::Down,
            Key::Down,
            Key::Clear,
            Key::Backspace,
            Key::Character('x'),
        ],
    );
    assert_eq!(e.editor.as_ref().unwrap().choice, Some(2));
    assert!(!e.step(Key::Quit));
    assert_eq!(e.spec.value["address"]["kind"], 1);
    keys(&mut e, &[Key::Enter]);
    assert_eq!(e.spec.value["address"]["kind"], 2);
}

#[test]
fn invalid_choices_are_rejected() {
    let source: Value = serde_json::from_str(include_str!("../../tests/person.json")).unwrap();
    for replacement in [json!(-1), json!(3), json!(1.5), json!("1"), json!(null)] {
        let mut v = source.clone();
        v["value"]["address"]["kind"] = replacement;
        assert!(Engine::parse(&v.to_string()).is_err());
    }
    for options in [json!([]), json!(["Home", "Home", "Other"])] {
        let mut v = source.clone();
        v["schema"]["fields"][2]["type"]["fields"][2]["type"]["options"] = options;
        assert!(Engine::parse(&v.to_string()).is_err());
    }
    let mut v = source;
    v["form"]["children"]["address"]["children"]["kind"]["widget"] = json!("text");
    assert!(Engine::parse(&v.to_string()).is_err());
}

#[test]
fn invalid_specifications_are_rejected_before_rendering() {
    let source: Value = serde_json::from_str(include_str!("../../tests/person.json")).unwrap();
    for (path, replacement) in [
        ("/version", json!(2)),
        ("/value/address/number", json!(-1)),
        ("/value/address", json!(["street"])),
        ("/form/children/name/widget", json!("checkbox")),
        (
            "/form/children/address/children/street/condition/path",
            json!(["address"]),
        ),
        (
            "/form/children/address/children/street/condition/path",
            json!(["name"]),
        ),
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
fn groups_allow_zero_and_one_child_and_reject_shape_mismatches() {
    for (children, fields, value) in [
        (json!([]), json!({}), json!({})),
        (
            json!([{"name":"only","type":{"kind":"text"}}]),
            json!({"only":{"kind":"field","label":"Only","widget":"textInput"}}),
            json!({"only":"only"}),
        ),
    ] {
        let spec = json!({"version":1,"schema":{"kind":"record","fields":children},
            "form":{"kind":"group","label":"Group","children":fields},"value":value});
        let e = Engine::parse(&spec.to_string()).unwrap();
        assert_eq!(e.fields().len(), value.as_object().unwrap().len());
        assert_eq!(serde_json::from_str::<Value>(&e.result()).unwrap(), value);
        let mut bad = spec.clone();
        bad["value"]["extra"] = json!("extra");
        assert!(Engine::parse(&bad.to_string()).is_err());
        let mut bad = spec;
        bad["form"]["children"]["extra"] =
            json!({"kind":"field","label":"Extra","widget":"textInput"});
        assert!(Engine::parse(&bad.to_string()).is_err());
    }
}

#[test]
fn hidden_root_and_visibility_changed_by_edit() {
    let spec = json!({"version":1,"schema":{"kind":"boolean"},"value":true,"form":{"kind":"visibleWhen","condition":{"kind":"project","path":[]},"body":{"kind":"field","label":"Visible","widget":"checkbox"}}});
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    keys(&mut e, &[Key::Enter]);
    assert!(e.fields().is_empty());
    assert_eq!(e.selected, 0);
    keys(
        &mut e,
        &[Key::Up, Key::Down, Key::Enter, Key::Character(' ')],
    );
    assert_eq!(e.result(), "false");
}
fn edit(engine: &mut Engine, input: &str) {
    keys(engine, &[Key::Enter, Key::Clear]);
    text(engine, input);
    keys(engine, &[Key::Enter]);
}
#[test]
fn repeated_items_add_remove_and_edit() {
    let mut e = Engine::parse(include_str!("../../tests/invoice.json")).unwrap();
    assert_eq!(e.fields().len(), 5);
    e.selected = 4;
    keys(&mut e, &[Key::Enter]);
    assert_eq!(e.fields().len(), 9);
    edit(&mut e, "Second");
    e.selected = 5;
    edit(&mut e, "0");
    e.selected = 3;
    keys(&mut e, &[Key::Enter]);
    assert_eq!(
        e.spec.value,
        json!([{"description":"Second","quantity":"0","unitPrice":"100"}])
    );
    e.selected = 1;
    edit(&mut e, "2");
    e.selected = 3;
    keys(&mut e, &[Key::Enter]);
    assert_eq!(e.fields().len(), 1);
    assert_eq!(e.spec.value, json!([]));
    keys(&mut e, &[Key::Enter]);
    assert_eq!(
        e.spec.value,
        json!([{"description":"New item","quantity":"1","unitPrice":"100"}])
    );
    assert!(!e.step(Key::Character('q')));
}

#[test]
fn nested_lists_and_item_visibility_use_local_scope() {
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/invoice.json")).unwrap();
    let item = spec["form"]["item"].clone();
    spec["form"]["item"] = json!({"kind":"visibleWhen", "condition":{
        "kind":"natLe", "left":{"kind":"value", "type":{"kind":"natural"}, "value":"1"},
        "right":{"kind":"project", "path":["quantity"]}}, "body":item});
    let inner_schema = spec["schema"].clone();
    let inner_form = spec["form"].clone();
    let inner_value = spec["value"].clone();
    spec["schema"] = json!({"kind":"list", "element":inner_schema});
    spec["form"] = json!({"kind":"list", "label":"Invoices", "item":inner_form, "defaultItem":[]});
    spec["value"] = json!([inner_value]);
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    assert_eq!(e.fields().len(), 7);
    e.selected = 1;
    edit(&mut e, "0");
    assert_eq!(e.fields().len(), 4);
    assert_eq!(e.fields()[0].path, vec![Step::Item(0), Step::Item(0)]);
    e.selected = 3;
    keys(&mut e, &[Key::Enter]);
    assert_eq!(e.spec.value[1], json!([]));
    keys(&mut e, &[Key::Enter]);
    assert_eq!(
        e.spec.value[1],
        json!([{"description":"New item","quantity":"1","unitPrice":"100"}])
    );
}

#[test]
fn malformed_lists_and_defaults_are_rejected() {
    let source: Value = serde_json::from_str(include_str!("../../tests/invoice.json")).unwrap();
    for invalid in [json!(null), json!([1]), json!([["Name", "1"]])] {
        let mut spec = source.clone();
        spec["value"] = invalid;
        assert!(Engine::parse(&spec.to_string()).is_err());
    }
    let mut spec = source;
    spec["form"]["defaultItem"] = json!(false);
    assert!(Engine::parse(&spec.to_string()).is_err());
}

#[test]
fn all_list_items_are_evaluated_in_element_scope() {
    let expr: Expr = serde_json::from_value(json!({"kind":"all","items":{"kind":"project","path":[]},"predicate":{"kind":"natLe","left":{"kind":"value","type":{"kind":"natural"},"value":"1"},"right":{"kind":"project","path":[]}}})).unwrap();
    assert_eq!(
        expr.ty(&Ty::List {
            element: Box::new(Ty::Natural)
        })
        .unwrap(),
        Ty::Boolean
    );
    assert_eq!(expr.eval(&json!(["1", "2"])), true);
    assert_eq!(expr.eval(&json!(["1", "0"])), false);
}
