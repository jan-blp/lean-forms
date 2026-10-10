use super::*;
use serde_json::json;
fn person() -> Engine {
    Engine::parse(include_str!("../../tests/person.json")).unwrap()
}
fn thermostat() -> Engine {
    Engine::parse(include_str!("../../tests/thermostat.json")).unwrap()
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
fn edit(engine: &mut Engine, input: &str) {
    keys(engine, &[Key::Enter, Key::Clear]);
    text(engine, input);
    keys(engine, &[Key::Enter]);
}
#[test]
fn invalid_drafts_are_editable_but_not_submittable() {
    let mut e = thermostat();
    edit(&mut e, "16");
    assert!(e.editor.is_none());
    assert_eq!(e.spec.value, json!(["16", "18"]));
    assert_eq!(
        e.errors(),
        ["Away temperature (C): Away temperature must not exceed home temperature."]
    );
    assert!(e.step(Key::Character('q')));
    assert_eq!(e.result(), "null");
    keys(&mut e, &[Key::Down]);
    edit(&mut e, "16");
    assert!(e.errors().is_empty());
    assert!(!e.step(Key::Character('q')));
    assert_eq!(
        serde_json::from_str::<Value>(&e.result()).unwrap(),
        json!(["16", "16"])
    );
}
#[test]
fn age_rule_allows_endpoints_and_reports_invalid_values() {
    let mut e = person();
    keys(&mut e, &[Key::Down]);
    for invalid in ["17", "121"] {
        edit(&mut e, invalid);
        assert_eq!(e.spec.value[1], invalid);
        assert_eq!(e.errors().len(), 1);
        assert!(e.errors()[0].contains("18 and 120"));
        assert!(e.step(Key::Character('q')));
    }
    for valid in ["18", "120"] {
        edit(&mut e, valid);
        assert!(e.errors().is_empty());
    }
    assert!(!e.step(Key::Character('q')));
}
#[test]
fn parsing_errors_stay_in_editor_and_cancellation_discards_draft() {
    let mut e = thermostat();
    for invalid in ["", "-1", "1.5", "abc", "+2"] {
        if e.editor.is_some() {
            keys(&mut e, &[Key::Escape]);
        }
        edit(&mut e, invalid);
        assert_eq!(
            e.editor.as_ref().unwrap().error.as_deref(),
            Some("Enter a non-negative whole number.")
        );
        assert_eq!(e.spec.value[0], "22");
    }
    keys(&mut e, &[Key::Escape]);
    edit(&mut e, " 0016 ");
    assert_eq!(e.spec.value[0], "16");
    assert!(!e.step(Key::Character('x')));
    assert_eq!(e.result(), "null");
    let mut e = person();
    assert!(!e.step(Key::Quit));
    assert_eq!(e.result(), "null");
}
#[test]
fn invalid_initial_and_hidden_fields_still_validate() {
    let mut spec: Value =
        serde_json::from_str(include_str!("../../tests/thermostat.json")).unwrap();
    spec["value"] = json!(["0", "18"]);
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    assert_eq!(e.errors().len(), 2);
    edit(&mut e, "22");
    assert!(!e.step(Key::Character('q')));
    let body = spec["form"].clone();
    spec["form"] = json!({"kind":"visibleWhen", "condition":{"kind":"value", "type":{"kind":"boolean"}, "value":false}, "body":body});
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    assert!(e.fields().is_empty());
    assert_eq!(e.errors().len(), 2);
    assert!(e.step(Key::Character('q')));
    assert!(!e.step(Key::Escape));
    assert_eq!(e.result(), "null");
}
#[test]
fn schema_constraints_and_error_locations_are_type_checked() {
    let source: Value = serde_json::from_str(include_str!("../../tests/thermostat.json")).unwrap();
    for (path, replacement) in [
        ("/version", json!(1)),
        (
            "/constraints/0/condition",
            json!({"kind":"project", "path":[0]}),
        ),
        ("/constraints/2/condition/left/path", json!([2])),
        ("/constraints/2/errorLocation", json!([0, 0])),
        ("/value/0", json!(-1)),
        ("/form/children/0/control", json!("checkbox")),
    ] {
        let mut spec = source.clone();
        *spec.pointer_mut(path).unwrap() = replacement;
        assert!(Engine::parse(&spec.to_string()).is_err(), "{path}");
    }
    assert!(Engine::parse("{}").is_err());
    let mut spec = source;
    spec["constraints"][0]["unknown"] = json!(true);
    assert!(Engine::parse(&spec.to_string()).is_err());
}
#[test]
fn visibility_choice_and_text_editing_still_work() {
    let mut e = person();
    assert_eq!(e.fields().len(), 4);
    keys(&mut e, &[Key::Down, Key::Down, Key::Character(' ')]);
    assert_eq!(e.fields().len(), 5);
    keys(&mut e, &[Key::Down]);
    edit(&mut e, "Elm Street");
    keys(&mut e, &[Key::Up, Key::Character(' ')]);
    assert_eq!(e.fields().len(), 4);
    assert_eq!(e.spec.value[3][0], "Elm Street");
    keys(&mut e, &[Key::Down, Key::Enter, Key::Down, Key::Escape]);
    assert_eq!(e.spec.value[3][1], 0);
    keys(&mut e, &[Key::Enter, Key::Up, Key::Down, Key::Enter]);
    assert_eq!(e.spec.value[3][1], 1);
    assert_eq!(e.shown(&e.fields()[3]), "Work");
    e.selected = 0;
    edit(&mut e, "qjx界");
    assert_eq!(e.spec.value[0], "qjx界");
    edit(&mut e, "");
    assert_eq!(e.spec.value[0], "");
}
#[test]
fn arbitrary_precision_constraints_and_all_predicates() {
    let mut spec: Value =
        serde_json::from_str(include_str!("../../tests/thermostat.json")).unwrap();
    // Keep only the cross-field constraint to exercise unrestricted naturals.
    spec["constraints"] = json!([spec["constraints"][2].clone()]);
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    let huge = "12345678901234567890123456789012345678901234567890";
    edit(&mut e, huge);
    assert!(e.errors().is_empty());
    keys(&mut e, &[Key::Down]);
    edit(&mut e, &format!("{huge}0"));
    assert_eq!(e.errors().len(), 1);
    edit(&mut e, huge);
    assert!(e.errors().is_empty());
    let expr: Expr = serde_json::from_value(json!({"kind":"and", "left":{"kind":"value", "type":{"kind":"boolean"}, "value":true}, "right":{"kind":"value", "type":{"kind":"boolean"}, "value":true}})).unwrap();
    assert_eq!(expr.ty(&Ty::Natural).unwrap(), Ty::Boolean);
    assert_eq!(expr.eval(&json!("1")), true);
}
#[test]
fn malformed_choices_are_rejected() {
    let source: Value = serde_json::from_str(include_str!("../../tests/person.json")).unwrap();
    for invalid in [json!(-1), json!(3), json!(1.5), json!("1"), json!(null)] {
        let mut spec = source.clone();
        spec["value"][3][1] = invalid;
        assert!(Engine::parse(&spec.to_string()).is_err());
    }
    for options in [json!([]), json!(["Home", "Home", "Other"])] {
        let mut spec = source.clone();
        spec["schema"]["right"]["right"]["right"]["right"]["options"] = options;
        assert!(Engine::parse(&spec.to_string()).is_err());
    }
}
