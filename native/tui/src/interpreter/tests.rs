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
fn scalar(kind: &str, widget: &str, value: Value) -> Engine {
    Engine::parse(&json!({"version":1,"schema":{"kind":kind},"form":{"kind":"field","label":"Value","widget":widget},"value":value}).to_string()).unwrap()
}
#[test]
fn natural_edits_validate_and_preserve_value_on_error() {
    let mut e = scalar("natural", "naturalInput", json!("12"));
    keys(&mut e, &[Key::Enter]);
    for invalid in ["", "-1", "1.5", "abc", "+2"] {
        keys(&mut e, &[Key::Clear]);
        text(&mut e, invalid);
        keys(&mut e, &[Key::Enter]);
        assert_eq!(e.editor.as_ref().unwrap().error.as_deref(), Some("Enter a non-negative whole number."));
        assert_eq!(e.spec.value, "12");
    }
    keys(&mut e, &[Key::Clear]);
    text(&mut e, " 0042 ");
    keys(&mut e, &[Key::Enter]);
    assert_eq!(e.spec.value, "42");
}
#[test]
fn checkbox_toggles_without_opening_editor() {
    let mut e = scalar("boolean", "checkbox", json!(false));
    keys(&mut e, &[Key::Character(' ')]);
    assert_eq!(e.spec.value, true);
    assert!(e.editor.is_none());
    keys(&mut e, &[Key::Enter]);
    assert_eq!(e.spec.value, false);
}
#[test]
fn cancellation_unicode_empty_text_and_quit() {
    let mut e = person();
    keys(&mut e, &[Key::Enter, Key::Clear]);
    text(&mut e, "changed");
    keys(&mut e, &[Key::Escape]);
    assert_eq!(e.spec.value, "Ada");
    keys(&mut e, &[Key::Enter, Key::Clear]);
    text(&mut e, "é");
    keys(&mut e, &[Key::Backspace]);
    text(&mut e, "qjki\0界");
    keys(&mut e, &[Key::Enter]);
    assert_eq!(e.spec.value, "qjki\0界");
    keys(&mut e, &[Key::Enter, Key::Clear, Key::Enter]);
    assert_eq!(e.spec.value, "");
    keys(&mut e, &[Key::Enter]);
    text(&mut e, "discarded");
    assert!(!e.step(Key::Quit));
    assert_eq!(e.spec.value, "");
    let mut e = person();
    assert!(!e.step(Key::Character('q')));
}
#[test]
fn predicates_and_unbounded_naturals() {
    let expr: Expr = serde_json::from_value(json!({"kind":"and", "left":{"kind":"value", "type":{"kind":"boolean"}, "value":true}, "right":{"kind":"natLe","left":{"kind":"value","type":{"kind":"natural"},"value":"10"},"right":{"kind":"project","path":[]}}})).unwrap();
    assert_eq!(expr.ty(&Ty::Natural).unwrap(), Ty::Boolean);
    let big = "12345678901234567890123456789012345678901234567890";
    assert_eq!(expr.eval(&json!(big)), true);
    assert_eq!(expr.eval(&json!("0009")), false);
    let mut e = scalar("natural", "naturalInput", json!("12"));
    keys(&mut e, &[Key::Enter, Key::Clear]);
    text(&mut e, big);
    keys(&mut e, &[Key::Enter]);
    assert_eq!(e.spec.value, big);
    let invalid: Expr = serde_json::from_value(json!({"kind":"project","path":[0]})).unwrap();
    assert!(invalid.ty(&Ty::Natural).is_err());
}
#[test]
fn invalid_specifications_are_rejected_before_rendering() {
    let source: Value = serde_json::from_str(include_str!("../../tests/person.json")).unwrap();
    for (path, replacement) in [
        ("/version", json!(2)),
        ("/value", json!(42)),
        ("/form/widget", json!("checkbox")),
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
