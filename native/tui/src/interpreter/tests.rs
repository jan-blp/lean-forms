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
    assert_eq!(e.fields().len(), 2);
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
    let input = Ty::Record {
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
    assert_eq!(expr.ty(&input).unwrap(), Ty::Boolean);
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
    keys(
        &mut e,
        &[
            Key::Down,
            Key::Character(' '),
            Key::Down,
            Key::Down,
            Key::Down,
            Key::Enter,
        ],
    );
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
    v["form"]["children"][2]["body"]["children"][2]["widget"] = json!("text");
    assert!(Engine::parse(&v.to_string()).is_err());
}

#[test]
fn invalid_specifications_are_rejected_before_rendering() {
    let source: Value = serde_json::from_str(include_str!("../../tests/person.json")).unwrap();
    for (path, replacement) in [
        ("/version", json!(2)),
        ("/value/address/number", json!(-1)),
        ("/value/address", json!(["street"])),
        ("/form/children/0/widget", json!("checkbox")),
        ("/form/children/2/condition/path", json!(["address"])),
        ("/form/children/2/condition/path", json!(["name"])),
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
fn stacks_allow_zero_and_one_child_and_validate_paths() {
    for children in [
        json!([]),
        json!([{"kind":"field","path":["only"],"schema":{"kind":"text"},"label":"Only","widget":"textInput"}]),
    ] {
        let spec = json!({"version":4,"schema":{"kind":"record","fields":[{"name":"only","type":{"kind":"text"}}]},
            "form":{"kind":"stack","label":"Group","children":children},"value":{"only":"only"}});
        let e = Engine::parse(&spec.to_string()).unwrap();
        assert_eq!(e.fields().len(), children.as_array().unwrap().len());
        assert_eq!(
            serde_json::from_str::<Value>(&e.result()).unwrap(),
            spec["value"]
        );
        let mut bad = spec.clone();
        bad["value"]["extra"] = json!("extra");
        assert!(Engine::parse(&bad.to_string()).is_err());
        let mut bad = spec;
        bad["form"]["children"].as_array_mut().unwrap().push(json!({"kind":"field","path":["missing"],"schema":{"kind":"text"},"label":"Extra","widget":"textInput"}));
        assert!(Engine::parse(&bad.to_string()).is_err());
    }
}

#[test]
fn hidden_root_and_visibility_changed_by_edit() {
    let spec = json!({"version":4,"schema":{"kind":"boolean"},"value":true,"form":{"kind":"visibleWhen","condition":{"kind":"project","path":[]},"body":{"kind":"field","path":[],"schema":{"kind":"boolean"},"label":"Visible","widget":"checkbox"}}});
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
    spec["form"] = json!({"kind":"list","path":[],"schema":spec["schema"],"label":"Invoices", "item":inner_form, "defaultItem":[]});
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
    let spec = serde_json::json!({"version":4, "schema":{"kind":"date"}, "form":{"kind":"field","path":[],"schema":{"kind":"date"},"label":"Date","widget":"dateInput"}, "value":"2028-02-28"});
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

#[test]
fn country_selects_city_type_and_preserves_each_selection() {
    let mut e = Engine::parse(include_str!("../../tests/location.json")).unwrap();
    assert_eq!(e.fields()[0].title, "Country");
    assert_eq!(e.fields()[1].title, "City");
    assert_eq!(e.fields()[1].options, ["Paris", "Lyon", "Marseille"]);
    e.selected = 1;
    keys(&mut e, &[Key::Enter, Key::Down, Key::Enter]);
    assert_eq!(e.shown(&e.fields()[1]), "Lyon");
    e.selected = 0;
    select_constructor(&mut e, 1);
    assert_eq!(e.fields()[1].options, ["Tokyo", "Kyoto", "Osaka"]);
    assert_eq!(e.shown(&e.fields()[1]), "Tokyo");
    e.selected = 1;
    keys(&mut e, &[Key::Enter, Key::Down, Key::Enter]);
    e.selected = 0;
    select_constructor(&mut e, 0);
    assert_eq!(e.shown(&e.fields()[1]), "Lyon");
    select_constructor(&mut e, 1);
    assert_eq!(e.shown(&e.fields()[1]), "Kyoto");
    assert!(!e.step(Key::Character('q')));
    assert_eq!(
        serde_json::from_str::<Value>(&e.result()).unwrap(),
        json!({"tag":"Japan", "value":1})
    );
}

fn shapes_spec() -> Value {
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/shapes.json")).unwrap();
    spec["value"] = json!({"tag":"dot","value":{}});
    spec
}

fn select_constructor(e: &mut Engine, index: usize) {
    keys(e, &[Key::Enter]);
    for _ in 0..e.editor.as_ref().unwrap().options.len() {
        keys(e, &[Key::Up]);
    }
    for _ in 0..index {
        keys(e, &[Key::Down]);
    }
    keys(e, &[Key::Enter]);
}

#[test]
fn sums_in_lists_preserve_the_correct_cache_after_removal() {
    let source = shapes_spec();
    let mut spec = source.clone();
    spec["schema"] = json!({"kind":"list","element":source["schema"]});
    spec["form"] = json!({"kind":"list","path":[],"schema":spec["schema"],"label":"Shapes","item":source["form"],"defaultItem":source["value"]});
    spec["value"] = json!([source["value"], source["value"]]);
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    for (selector, width) in [(0, "6"), (2, "9")] {
        e.selected = selector;
        select_constructor(&mut e, 2);
        e.selected = selector + 1;
        edit(&mut e, width);
        e.selected = selector;
        select_constructor(&mut e, 0);
    }
    e.selected = 1;
    keys(&mut e, &[Key::Enter]); // Remove first shape; the second cache moves with it.
    e.selected = 0;
    select_constructor(&mut e, 2);
    assert_eq!(e.spec.value[0]["value"]["width"], "9");
    e.selected = 4;
    keys(&mut e, &[Key::Enter]); // A new item must not inherit an old cache.
    select_constructor(&mut e, 2);
    assert_eq!(e.spec.value[1]["value"]["width"], "4");
}

#[test]
fn nested_sums_and_visibility_use_constructor_local_scope() {
    let source = shapes_spec();
    let mut spec = source.clone();
    // The outer sum has two identical sum payload types. Their caches must stay separate.
    spec["schema"] = json!({"kind":"sum", "constructors":[{"name":"a","type":source["schema"]},{"name":"b","type":source["schema"]}]});
    spec["form"] = json!({"kind":"sum","path":[],"schema":spec["schema"],"label":"Shape",
        "branches":{"a":source["form"],"b":source["form"]}, "defaults":{"a":source["value"],"b":source["value"]}});
    spec["value"] = json!({"tag":"a","value":source["value"]});
    // Visibility sees the selected inner payload, not the outer sum.
    for index in ["a", "b"] {
        let branch = spec["form"]["branches"][index]["branches"]["rectangle"].clone();
        spec["form"]["branches"][index]["branches"]["rectangle"] = json!({"kind":"visibleWhen",
            "condition":{"kind":"natLe","left":{"kind":"value","type":{"kind":"natural"},"value":"1"},"right":{"kind":"project","path":["height"]}},"body":branch});
    }
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    e.selected = 1;
    select_constructor(&mut e, 2);
    e.selected = 2;
    edit(&mut e, "8");
    e.selected = 1;
    select_constructor(&mut e, 0);
    e.selected = 0;
    select_constructor(&mut e, 1);
    e.selected = 1;
    select_constructor(&mut e, 2);
    assert_eq!(e.spec.value["value"]["value"]["width"], "4");
    e.selected = 0;
    select_constructor(&mut e, 0);
    e.selected = 1;
    select_constructor(&mut e, 2);
    assert_eq!(e.spec.value["value"]["value"]["width"], "8");
    e.selected = 3;
    edit(&mut e, "0");
    assert_eq!(e.fields().len(), 2);
}

#[test]
fn cases_support_typed_results_and_only_evaluate_the_selected_branch() {
    let spec = shapes_spec();
    let input: Ty = serde_json::from_value(spec["schema"].clone()).unwrap();
    let dimension = json!({"kind":"cases", "type":{"kind":"natural"},
        "subject":{"kind":"project","path":[]},
        "branches":{"dot":{"kind":"value","type":{"kind":"natural"},"value":"0"},
                    "circle":{"kind":"project","path":[]}, "rectangle":{"kind":"project","path":["height"]}}});
    let expr: Expr = serde_json::from_value(dimension.clone()).unwrap();
    assert_eq!(expr.ty(&input).unwrap(), Ty::Natural);
    // Evaluating the rectangle branch on Dot would access a missing field.
    assert_eq!(expr.eval(&json!({"tag":"dot","value":{}})), "0");
    assert_eq!(
        expr.eval(&json!({"tag":"rectangle","value":{"width":"7","height":"2"}})),
        "2"
    );
    let condition: Expr = serde_json::from_value(json!({"kind":"natLe","left":dimension,
        "right":{"kind":"value","type":{"kind":"natural"},"value":"1"}}))
    .unwrap();
    assert_eq!(condition.ty(&input).unwrap(), Ty::Boolean);
    assert_eq!(
        condition.eval(&json!({"tag":"rectangle","value":{"width":"7","height":"2"}})),
        false
    );
    for (ty, value) in [
        (json!({"kind":"text"}), json!("Dot")),
        (json!({"kind":"record","fields":[]}), json!({})),
        (spec["schema"].clone(), spec["value"].clone()),
    ] {
        let branch = json!({"kind":"value","type":ty,"value":value});
        let expr: Expr = serde_json::from_value(json!({"kind":"cases","type":ty,
            "subject":{"kind":"project","path":[]},"branches":{"dot":branch,"circle":branch,"rectangle":branch}}))
        .unwrap();
        assert_eq!(
            expr.ty(&input).unwrap(),
            serde_json::from_value::<Ty>(ty).unwrap()
        );
        assert_eq!(expr.eval(&spec["value"]), value);
    }
    for (path, replacement) in [
        ("/type", json!({"kind":"boolean"})),
        ("/branches", json!({})),
        (
            "/branches",
            json!({"dot":dimension["branches"]["dot"], "circle":dimension["branches"]["circle"],
                "rectangle":dimension["branches"]["rectangle"], "extra":dimension["branches"]["dot"]}),
        ),
        ("/branches/circle/path", json!(["missing"])),
        (
            "/branches/circle",
            json!({"kind":"value","type":{"kind":"text"},"value":"wrong"}),
        ),
    ] {
        let mut invalid = dimension.clone();
        *invalid.pointer_mut(path).unwrap() = replacement;
        let expr: Expr = serde_json::from_value(invalid).unwrap();
        assert!(expr.ty(&input).is_err(), "{path}");
    }
}

#[test]
fn duplicate_schema_names_are_rejected_even_in_inactive_payloads() {
    let source = shapes_spec();
    for pointer in [
        "/schema/constructors/1/name",
        "/schema/constructors/2/type/fields/1/name",
    ] {
        let mut spec = source.clone();
        *spec.pointer_mut(pointer).unwrap() = json!(if pointer.contains("fields") {
            "width"
        } else {
            "dot"
        });
        assert!(Engine::parse(&spec.to_string()).is_err());
    }
}
