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
    assert_eq!(e.fields().len(), 2);
    assert_eq!(e.spec.value["address"]["number"], "42");
    keys(&mut e, &[Key::Character(' ')]);
    assert_eq!(e.fields().len(), 4);
    assert_eq!(
        serde_json::from_str::<Value>(&e.result()).unwrap(),
        json!({"name":"Ada","subscribed":true,"address":{"street":"Lambda Lane","number":"42"}})
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
fn invalid_specifications_are_rejected_before_rendering() {
    let source: Value = serde_json::from_str(include_str!("../../tests/person.json")).unwrap();
    for (path, replacement) in [
        ("/version", json!(2)),
        ("/value/address/number", json!(-1)),
        ("/value/address", json!(["street"])),
        ("/form/children/name/widget", json!("checkbox")),
        ("/form/children/address/condition/path", json!(["address"])),
        ("/form/children/address/condition/path", json!(["name"])),
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

#[test]
fn date_calendar_rules_and_picker_modes() {
    let cases: Value = serde_json::from_str(include_str!("../../tests/dates.json")).unwrap();
    for value in cases["valid"].as_array().unwrap() {
        assert_eq!(
            date(value.as_str().unwrap()).unwrap().to_string(),
            value.as_str().unwrap()
        );
    }
    for value in cases["invalid"].as_array().unwrap() {
        assert!(date(value.as_str().unwrap()).is_none());
    }
    let spec = serde_json::json!({"version":1, "schema":{"kind":"date"}, "form":{"kind":"field","label":"Date","widget":"dateInput"}, "value":"2028-02-28"});
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    e.step(Key::Enter);
    e.step(Key::Character('l'));
    assert_eq!(e.editor.as_ref().unwrap().text, "2028-02-29");
    e.step(Key::Enter);
    assert!(e.editor.as_ref().unwrap().date_input);
    e.step(Key::Enter);
    assert!(e.editor.is_none());
    assert_eq!(e.spec.value, "2028-02-29");
}
