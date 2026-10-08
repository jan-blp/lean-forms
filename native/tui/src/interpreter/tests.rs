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
fn edits_validate_and_preserve_other_values() {
    let mut e = person();
    assert_eq!(e.fields().len(), 5);
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
    assert_eq!(e.fields().len(), 5);
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
    keys(&mut e, &[Key::Down, Key::Down, Key::Down, Key::Down, Key::Enter]);
    assert_eq!(
        e.editor.as_ref().unwrap().options,
        ["Home", "Work", "Other"]
    );
    keys(&mut e, &[Key::Up, Key::Character('j'), Key::Escape]);
    assert_eq!(e.spec.value["address"]["kind"], 0);
    keys(&mut e, &[Key::Enter, Key::Down, Key::Enter]);
    assert_eq!(e.spec.value["address"]["kind"], 1);
    assert_eq!(e.shown(&e.fields()[4]), "Work");
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
