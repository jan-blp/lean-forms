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
        assert_eq!(e.spec.value[2][1], "12");
    }
    keys(&mut e, &[Key::Clear]);
    text(&mut e, " 0042 ");
    keys(&mut e, &[Key::Enter, Key::Up, Key::Up, Key::Character(' ')]);
    assert_eq!(e.fields().len(), 3);
    assert_eq!(e.spec.value[2][1], "42");
    keys(&mut e, &[Key::Character(' ')]);
    assert_eq!(e.fields().len(), 5);
    assert_eq!(
        serde_json::from_str::<Value>(&e.result()).unwrap(),
        json!(["Ada", true, ["Lambda Lane", "42", 0]])
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
    let root = Ty::Group {
        children: vec![Ty::Text, Ty::Natural],
    };
    let expr: Expr = serde_json::from_value(json!({"kind":"and", "left":{"kind":"value", "type":{"kind":"boolean"}, "value":true}, "right":{"kind":"natLe","left":{"kind":"value","type":{"kind":"natural"},"value":"10"},"right":{"kind":"project","path":[1]}}})).unwrap();
    assert_eq!(expr.ty(&root).unwrap(), Ty::Boolean);
    assert_eq!(
        expr.eval(&json!([
            "Ada",
            "10000000000000000000000000000000000000000000000"
        ])),
        true
    );
    assert_eq!(expr.eval(&json!(["Ada", "0009"])), false);
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
    assert_eq!(e.spec.value[2][1], big);
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
    assert_eq!(e.spec.value[2][2], 0);
    keys(&mut e, &[Key::Enter, Key::Down, Key::Enter]);
    assert_eq!(e.spec.value[2][2], 1);
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
    assert_eq!(e.spec.value[2][2], 1);
    keys(&mut e, &[Key::Enter]);
    assert_eq!(e.spec.value[2][2], 2);
}

#[test]
fn invalid_choices_are_rejected() {
    let source: Value = serde_json::from_str(include_str!("../../tests/person.json")).unwrap();
    for replacement in [json!(-1), json!(3), json!(1.5), json!("1"), json!(null)] {
        let mut v = source.clone();
        v["value"][2][2] = replacement;
        assert!(Engine::parse(&v.to_string()).is_err());
    }
    for options in [json!([]), json!(["Home", "Home", "Other"])] {
        let mut v = source.clone();
        v["schema"]["children"][2]["children"][2]["options"] = options;
        assert!(Engine::parse(&v.to_string()).is_err());
    }
    let mut v = source;
    v["form"]["children"][2]["children"][2]["control"] = json!("text");
    assert!(Engine::parse(&v.to_string()).is_err());
}

#[test]
fn invalid_specifications_are_rejected_before_rendering() {
    let source: Value = serde_json::from_str(include_str!("../../tests/person.json")).unwrap();
    for (path, replacement) in [
        ("/version", json!(2)),
        ("/value/2/1", json!(-1)),
        ("/value/2", json!(["street"])),
        ("/form/children/0/control", json!("checkbox")),
        ("/form/children/2/children/0/condition/path", json!([2])),
        ("/form/children/2/children/0/condition/path", json!([0])),
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
        (json!([]), json!([]), json!([])),
        (
            json!([{"kind":"text"}]),
            json!([{"kind":"field","label":"Only","control":"text"}]),
            json!(["only"]),
        ),
    ] {
        let spec = json!({"version":1,"schema":{"kind":"group","children":children},
            "form":{"kind":"group","label":"Group","children":fields},"value":value});
        let e = Engine::parse(&spec.to_string()).unwrap();
        assert_eq!(e.fields().len(), value.as_array().unwrap().len());
        assert_eq!(serde_json::from_str::<Value>(&e.result()).unwrap(), value);
        let mut bad = spec.clone();
        bad["value"].as_array_mut().unwrap().push(json!("extra"));
        assert!(Engine::parse(&bad.to_string()).is_err());
        let mut bad = spec;
        bad["form"]["children"]
            .as_array_mut()
            .unwrap()
            .push(json!({"kind":"field","label":"Extra","control":"text"}));
        assert!(Engine::parse(&bad.to_string()).is_err());
    }
}

#[test]
fn hidden_root_and_visibility_changed_by_edit() {
    let spec = json!({"version":1,"schema":{"kind":"boolean"},"value":true,"form":{"kind":"visibleWhen","condition":{"kind":"project","path":[]},"body":{"kind":"field","label":"Visible","control":"checkbox"}}});
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
