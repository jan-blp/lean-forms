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
    keys(engine, &[Key::Enter]);
    if engine
        .editor
        .as_ref()
        .is_some_and(|editor| editor.calendar.is_some())
    {
        keys(engine, &[Key::Character('i')]);
    }
    keys(engine, &[Key::Clear]);
    text(engine, input);
    keys(engine, &[Key::Enter]);
}
#[test]
fn repeated_items_add_remove_edit_and_validate() {
    let mut e = Engine::parse(include_str!("../../tests/invoice.json")).unwrap();
    assert_eq!(e.fields().len(), 7);
    e.selected = 5;
    keys(&mut e, &[Key::Enter]);
    assert_eq!(e.fields().len(), 12);
    edit(&mut e, "Second");
    e.selected = 6;
    edit(&mut e, "0");
    assert_eq!(e.errors().len(), 1);
    assert!(e.step(Key::Character('q')));
    e.selected = 4;
    keys(&mut e, &[Key::Enter]);
    assert_eq!(
        e.spec.value,
        json!([{"description":"Second", "quantity":"0", "unitPrice":"100"}])
    );
    e.selected = 1;
    edit(&mut e, "2");
    assert!(e.errors().is_empty());
    e.selected = 4;
    keys(&mut e, &[Key::Enter]);
    assert_eq!(e.fields().len(), 2);
    assert_eq!(e.spec.value, json!([]));
    e.selected = 0;
    keys(&mut e, &[Key::Enter]);
    assert_eq!(
        e.spec.value,
        json!([{"description":"New item", "quantity":"1", "unitPrice":"100"}])
    );
    assert!(!e.step(Key::Character('q')));
}

#[test]
fn nested_lists_and_item_visibility_use_local_scope() {
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/invoice.json")).unwrap();
    let item = spec["form"]["children"][0]["item"].clone();
    spec["form"]["children"][0]["item"] = json!({"kind":"visibleWhen", "condition":{
        "kind":"natLe", "left":{"kind":"value", "type":{"kind":"natural"}, "value":"1"},
        "right":{"kind":"project", "path":["quantity"]}}, "body":item});
    let inner_schema = spec["schema"].clone();
    let inner_form = spec["form"].clone();
    let inner_value = spec["value"].clone();
    spec["schema"] = json!({"kind":"list", "element":inner_schema});
    spec["form"] = json!({"kind":"list", "path":[], "schema":spec["schema"], "label":"Invoices", "item":inner_form, "defaultItem":[]});
    spec["value"] = json!([inner_value]);
    spec["constraints"] = json!([]);
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    assert_eq!(e.fields().len(), 9);
    e.selected = 1;
    edit(&mut e, "0");
    assert_eq!(e.fields().len(), 5);
    assert_eq!(e.fields()[0].path, vec![Step::Item(0), Step::Item(0)]);
    e.selected = 4;
    keys(&mut e, &[Key::Enter]);
    assert_eq!(e.spec.value[1], json!([]));
    keys(&mut e, &[Key::Enter]);
    assert_eq!(
        e.spec.value[1],
        json!([{"description":"New item", "quantity":"1", "unitPrice":"100"}])
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
    spec["form"]["children"][0]["defaultItem"] = json!(false);
    assert!(Engine::parse(&spec.to_string()).is_err());
}

#[test]
fn invalid_drafts_are_editable_but_not_submittable() {
    let mut e = thermostat();
    edit(&mut e, "16");
    assert!(e.editor.is_none());
    assert_eq!(e.spec.value, json!({"home":"16", "away":"18"}));
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
        json!({"home":"16", "away":"16"})
    );
}
#[test]
fn age_rule_allows_endpoints_and_reports_invalid_values() {
    let mut e = person();
    keys(&mut e, &[Key::Down]);
    for invalid in ["17", "121"] {
        edit(&mut e, invalid);
        assert_eq!(e.spec.value["age"], invalid);
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
        assert_eq!(e.spec.value["home"], "22");
    }
    keys(&mut e, &[Key::Escape]);
    edit(&mut e, " 0016 ");
    assert_eq!(e.spec.value["home"], "16");
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
    spec["value"] = json!({"home":"0", "away":"18"});
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
        ("/version", json!(2)),
        ("/version", json!(3)),
        (
            "/constraints/0/condition",
            json!({"kind":"project", "path":["home"]}),
        ),
        ("/constraints/2/condition/left/path", json!(["missing"])),
        ("/constraints/2/errorLocation", json!(["home", "home"])),
        ("/value/home", json!(-1)),
        ("/form/children/0/widget", json!("checkbox")),
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
    assert_eq!(e.fields().len(), 3);
    keys(&mut e, &[Key::Down, Key::Down, Key::Character(' ')]);
    assert_eq!(e.fields().len(), 5);
    keys(&mut e, &[Key::Down]);
    edit(&mut e, "Elm Street");
    keys(&mut e, &[Key::Up, Key::Character(' ')]);
    assert_eq!(e.fields().len(), 3);
    assert_eq!(e.spec.value["address"]["street"], "Elm Street");
    keys(
        &mut e,
        &[
            Key::Character(' '),
            Key::Down,
            Key::Down,
            Key::Enter,
            Key::Down,
            Key::Escape,
        ],
    );
    assert_eq!(e.spec.value["address"]["kind"], 0);
    keys(&mut e, &[Key::Enter, Key::Up, Key::Down, Key::Enter]);
    assert_eq!(e.spec.value["address"]["kind"], 1);
    assert_eq!(e.shown(&e.fields()[4]), "Work");
    e.selected = 0;
    edit(&mut e, "qjx界");
    assert_eq!(e.spec.value["name"], "qjx界");
    edit(&mut e, "");
    assert_eq!(e.spec.value["name"], "");
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
        spec["value"]["address"]["kind"] = invalid;
        assert!(Engine::parse(&spec.to_string()).is_err());
    }
    for options in [json!([]), json!(["Home", "Home", "Other"])] {
        let mut spec = source.clone();
        spec["schema"]["fields"][3]["type"]["fields"][1]["type"]["options"] = options;
        assert!(Engine::parse(&spec.to_string()).is_err());
    }
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
fn constructors_validate_only_active_payload_and_preserve_drafts() {
    let mut e = Engine::parse(&shapes_spec().to_string()).unwrap();
    assert_eq!(e.fields().len(), 1);
    assert_eq!(e.shown(&e.fields()[0]), "dot");
    keys(&mut e, &[Key::Enter, Key::Down, Key::Escape]);
    assert_eq!(e.spec.value, json!({"tag":"dot", "value":{}}));
    select_constructor(&mut e, 2);
    assert_eq!(e.fields().len(), 3);
    assert_eq!(e.shown(&e.fields()[0]), "rectangle");
    e.selected = 1;
    edit(&mut e, "7");
    e.selected = 2;
    edit(&mut e, "0");
    assert_eq!(e.errors().len(), 1);
    assert!(e.step(Key::Character('q')));
    e.selected = 0;
    select_constructor(&mut e, 0);
    assert!(e.errors().is_empty());
    select_constructor(&mut e, 2);
    assert_eq!(
        e.spec.value,
        json!({"tag":"rectangle","value":{"width":"7","height":"0"}})
    );
    assert_eq!(e.errors().len(), 1);
    e.selected = 2;
    edit(&mut e, "2");
    e.selected = 0;
    select_constructor(&mut e, 0);
    assert!(!e.step(Key::Character('q')));
    assert_eq!(
        serde_json::from_str::<Value>(&e.result()).unwrap(),
        json!({"tag":"dot","value":{}})
    );
}

#[test]
fn malformed_sums_and_inactive_branch_forms_are_rejected() {
    let source = shapes_spec();
    for invalid in [
        json!({}),
        json!([0, []]),
        json!({"tag":3,"value":[]}),
        json!({"tag":-1,"value":[]}),
        json!({"tag":"0","value":[]}),
        json!({"tag":"dot","value":false}),
        json!({"tag":"rectangle","value":{"width":"","height":false}}),
        json!({"tag":"dot","value":{},"extra":true}),
    ] {
        let mut spec = source.clone();
        spec["value"] = invalid;
        assert!(Engine::parse(&spec.to_string()).is_err());
    }
    for (path, invalid) in [
        ("/form/defaults/circle", json!([])),
        (
            "/form/branches/rectangle/children/0/widget",
            json!("checkbox"),
        ),
        ("/form/branches", json!([])),
        ("/constraints/0/condition/branches", json!([])),
        (
            "/constraints/0/condition/branches/circle",
            json!({"kind":"project","path":[0]}),
        ),
        (
            "/constraints/0/condition/subject",
            json!({"kind":"value","type":{"kind":"boolean"},"value":true}),
        ),
        ("/constraints/0/errorLocation", json!([0])),
    ] {
        let mut spec = source.clone();
        *spec.pointer_mut(path).unwrap() = invalid;
        assert!(Engine::parse(&spec.to_string()).is_err(), "{path}");
    }
}

#[test]
fn sums_in_lists_preserve_the_correct_cache_after_removal() {
    let source = shapes_spec();
    let mut spec = source.clone();
    spec["schema"] = json!({"kind":"list","element":source["schema"]});
    spec["form"] =
        json!({"kind":"list","path":[],"schema":spec["schema"],"label":"Shapes","item":source["form"],"defaultItem":source["value"]});
    spec["value"] = json!([source["value"], source["value"]]);
    spec["constraints"] = json!([]);
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
    spec["form"] = json!({"kind":"sum", "path":[], "schema":spec["schema"], "label":"Shape",
        "branches":{"a":source["form"],"b":source["form"]}, "defaults":{"a":source["value"],"b":source["value"]}});
    spec["value"] = json!({"tag":"a","value":source["value"]});
    spec["constraints"] = json!([]);
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
fn named_fields_and_constructors_survive_schema_reordering() {
    let mut spec: Value =
        serde_json::from_str(include_str!("../../tests/thermostat.json")).unwrap();
    spec["schema"]["fields"].as_array_mut().unwrap().reverse();
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    assert_eq!(e.fields()[0].title, "Home temperature (C)");
    e.selected = 1;
    edit(&mut e, "23");
    assert_eq!(e.spec.value, json!({"home":"22","away":"23"}));
    assert_eq!(e.errors().len(), 1);
    assert!(e.errors()[0].starts_with("Away temperature (C):"));

    let mut spec = shapes_spec();
    spec["schema"]["constructors"]
        .as_array_mut()
        .unwrap()
        .reverse();
    spec["form"]["schema"] = spec["schema"].clone();
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    assert_eq!(e.shown(&e.fields()[0]), "dot");
    select_constructor(&mut e, 0);
    assert_eq!(
        e.spec.value,
        json!({"tag":"rectangle","value":{"width":"4","height":"2"}})
    );
    e.selected = 1;
    edit(&mut e, "0");
    assert_eq!(e.errors().len(), 1);
    e.selected = 0;
    select_constructor(&mut e, 2);
    assert!(e.errors().is_empty());
    select_constructor(&mut e, 0);
    assert_eq!(e.spec.value["value"]["width"], "0");
}

#[test]
fn records_reject_missing_extra_and_unknown_fields() {
    let source: Value = serde_json::from_str(include_str!("../../tests/thermostat.json")).unwrap();
    for value in [
        json!([]),
        json!({}),
        json!({"home":"22"}),
        json!({"home":"22","wrong":"18"}),
        json!({"home":"22","away":"18","extra":true}),
    ] {
        let mut spec = source.clone();
        spec["value"] = value;
        assert!(Engine::parse(&spec.to_string()).is_err());
    }
    let mut spec = source.clone();
    spec["form"]["children"][1]["path"] = json!(["wrong"]);
    assert!(Engine::parse(&spec.to_string()).is_err());
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

#[test]
fn record_fields_named_tag_and_value_are_not_sum_payloads() {
    let spec = json!({"version":4,"constraints":[],
        "schema":{"kind":"record","fields":[{"name":"tag","type":{"kind":"text"}},
            {"name":"value","type":{"kind":"natural"}}]},
        "form":{"kind":"stack","label":"Record","children":[
            {"kind":"field","path":["tag"],"schema":{"kind":"text"},"label":"Tag","widget":"textInput"},
            {"kind":"field","path":["value"],"schema":{"kind":"natural"},"label":"Value","widget":"naturalInput"}]},
        "value":{"tag":"hello","value":"3"}});
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    edit(&mut e, "world");
    e.selected = 1;
    edit(&mut e, "4");
    assert!(!e.step(Key::Character('q')));
    assert_eq!(
        serde_json::from_str::<Value>(&e.result()).unwrap(),
        json!({"tag":"world","value":"4"})
    );
}

#[test]
fn display_order_changes_navigation_without_changing_values_or_validation() {
    let mut spec: Value =
        serde_json::from_str(include_str!("../../tests/thermostat.json")).unwrap();
    spec["form"]["children"].as_array_mut().unwrap().reverse();
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    assert_eq!(
        e.fields()
            .iter()
            .map(|field| field.title.as_str())
            .collect::<Vec<_>>(),
        ["Away temperature (C)", "Home temperature (C)"]
    );
    assert_eq!(e.shown(&e.fields()[0]), "18");
    edit(&mut e, "23");
    assert_eq!(e.spec.value, json!({"home":"22","away":"23"}));
    assert!(e.errors()[0].starts_with("Away temperature (C):"));
    assert!(e.step(Key::Character('q')));
    keys(&mut e, &[Key::Down]);
    edit(&mut e, "24");
    assert!(!e.step(Key::Character('q')));
    assert_eq!(
        serde_json::from_str::<Value>(&e.result()).unwrap(),
        json!({"home":"24","away":"23"})
    );
}

#[test]
fn display_order_applies_inside_lists_and_sum_payloads() {
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/invoice.json")).unwrap();
    spec["form"]["children"][0]["item"]["children"][0]["children"].as_array_mut().unwrap().rotate_right(1);
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    assert_eq!(e.fields()[0].title, "Unit price (cents)");
    edit(&mut e, "250");
    assert_eq!(e.spec.value[0]["unitPrice"], "250");
    e.selected = 5;
    keys(&mut e, &[Key::Enter]);
    assert_eq!(e.fields()[5].title, "Unit price (cents)");

    let mut spec = shapes_spec();
    spec["form"]["branches"]["rectangle"]["children"].as_array_mut().unwrap().reverse();
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    select_constructor(&mut e, 2);
    assert_eq!(e.fields()[1].title, "Height");
    e.selected = 1;
    edit(&mut e, "8");
    assert_eq!(e.spec.value["value"], json!({"width":"4", "height":"8"}));
    e.selected = 0;
    select_constructor(&mut e, 0);
    select_constructor(&mut e, 2);
    assert_eq!(e.shown(&e.fields()[1]), "8");
}

#[test]
fn hidden_components_still_validate_bound_paths() {
    let source: Value = serde_json::from_str(include_str!("../../tests/thermostat.json")).unwrap();
    for path in [json!(["unknown"]), json!(["home", "away"]), json!([0])] {
        let mut spec = source.clone();
        spec["form"]["children"][0]["path"] = path;
        spec["form"] = json!({"kind":"visibleWhen", "condition":boolean(false), "body":spec["form"]});
        assert!(Engine::parse(&spec.to_string()).is_err());
    }
}

fn disabled(condition: Value, body: Value) -> Value {
    json!({"kind":"disabledWhen", "condition":condition, "body":body})
}
fn boolean(value: bool) -> Value {
    json!({"kind":"value", "type":{"kind":"boolean"}, "value":value})
}

#[test]
fn disabled_controls_preserve_values_and_validation() {
    for fixture in [
        include_str!("../../tests/person.json"),
        include_str!("../../tests/invoice.json"),
        include_str!("../../tests/shapes.json"),
    ] {
        let mut spec: Value = serde_json::from_str(fixture).unwrap();
        spec["form"] = disabled(boolean(true), disabled(boolean(false), spec["form"].take()));
        let mut e = Engine::parse(&spec.to_string()).unwrap();
        let original = e.spec.value.clone();
        for index in 0..e.fields().len() {
            e.selected = index;
            assert!(e.fields()[index].presentation.disabled);
            keys(
                &mut e,
                &[Key::Enter, Key::Character('i'), Key::Character(' ')],
            );
            assert!(e.editor.is_none());
            assert_eq!(e.spec.value, original);
        }
    }
    let mut spec: Value =
        serde_json::from_str(include_str!("../../tests/thermostat.json")).unwrap();
    spec["value"]["home"] = json!("0");
    spec["form"] = disabled(boolean(true), spec["form"].take());
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    assert!(!e.errors().is_empty());
    assert!(e.step(Key::Character('q')));
}

#[test]
fn disabled_condition_reacts_to_edits_and_checks_types() {
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/person.json")).unwrap();
    spec["form"]["children"][0] = disabled(
        json!({"kind":"project", "path":["subscribed"]}),
        spec["form"]["children"][0].take(),
    );
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    assert!(!e.fields()[0].presentation.disabled);
    e.selected = 2;
    keys(&mut e, &[Key::Character(' ')]);
    assert!(e.fields()[0].presentation.disabled);
    keys(&mut e, &[Key::Character(' ')]);
    e.selected = 0;
    edit(&mut e, "Grace");
    assert_eq!(e.spec.value["name"], json!("Grace"));
    spec["form"]["children"][0]["condition"] = json!({"kind":"project", "path":["age"]});
    assert!(Engine::parse(&spec.to_string()).is_err());
}

#[test]
fn disabled_conditions_use_payload_and_item_scope() {
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/shapes.json")).unwrap();
    spec["value"] = json!({"tag":"circle", "value":"3"});
    let condition = json!({"kind":"natLe", "left":{"kind":"project", "path":[]}, "right":{"kind":"value", "type":{"kind":"natural"}, "value":"5"}});
    spec["form"]["branches"]["circle"] =
        disabled(condition, spec["form"]["branches"]["circle"].take());
    let e = Engine::parse(&spec.to_string()).unwrap();
    assert!(!e.fields()[0].presentation.disabled);
    assert!(e.fields()[1].presentation.disabled);
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/invoice.json")).unwrap();
    let condition = json!({"kind":"natLe", "left":{"kind":"project", "path":["quantity"]}, "right":{"kind":"value", "type":{"kind":"natural"}, "value":"5"}});
    spec["form"]["children"][0]["item"] = disabled(condition, spec["form"]["children"][0]["item"].take());
    let e = Engine::parse(&spec.to_string()).unwrap();
    assert!(e.fields()[0..4].iter().all(|f| f.presentation.disabled));
    assert!(e.fields()[4..].iter().all(|f| !f.presentation.disabled));
}

#[test]
fn negation_rejects_non_boolean_operands() {
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/person.json")).unwrap();
    spec["form"]["children"][3]["condition"] =
        json!({"kind":"project", "path":["age"]});
    assert!(Engine::parse(&spec.to_string()).is_err());
}

#[test]
fn computed_total_updates_and_is_never_submitted_or_edited() {
    let mut e = Engine::parse(include_str!("../../tests/invoice.json")).unwrap();
    let total = |e: &Engine| e.shown(e.fields().last().unwrap());
    assert_eq!(total(&e), "100");
    e.selected = 1;
    edit(&mut e, "3");
    assert_eq!(total(&e), "300");
    e.selected = 5;
    keys(&mut e, &[Key::Enter]);
    assert_eq!(total(&e), "400");
    e.selected = 4;
    keys(&mut e, &[Key::Enter]);
    assert_eq!(total(&e), "100");
    let value = e.spec.value.clone();
    e.selected = e.fields().len() - 1;
    keys(
        &mut e,
        &[Key::Enter, Key::Character('i'), Key::Character(' ')],
    );
    assert!(e.editor.is_none());
    assert_eq!(e.spec.value, value);
    assert!(!e.step(Key::Character('q')));
    assert_eq!(serde_json::from_str::<Value>(&e.result()).unwrap(), value);
    e.selected = 4;
    keys(&mut e, &[Key::Enter]);
    assert_eq!(total(&e), "0");
}

#[test]
fn computed_arithmetic_is_unbounded() {
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/invoice.json")).unwrap();
    // (10^40 - 1)^2 = 10^80 - 2*10^40 + 1.
    let n = "9".repeat(40);
    spec["value"][0]["quantity"] = json!(n);
    spec["value"][0]["unitPrice"] = json!(n);
    let e = Engine::parse(&spec.to_string()).unwrap();
    assert_eq!(
        e.shown(e.fields().last().unwrap()),
        format!("{}8{}1", "9".repeat(39), "0".repeat(39))
    );
    spec["value"] = json!([
        {"description":"Large", "quantity":"9".repeat(80), "unitPrice":"1"},
        {"description":"One", "quantity":"1", "unitPrice":"1"}
    ]);
    let e = Engine::parse(&spec.to_string()).unwrap();
    assert_eq!(
        e.shown(e.fields().last().unwrap()),
        format!("1{}", "0".repeat(80))
    );
}

#[test]
fn computed_expressions_are_checked_even_when_hidden() {
    let source: Value = serde_json::from_str(include_str!("../../tests/invoice.json")).unwrap();
    for expression in [
        json!({"kind":"project", "path":[]}),
        json!({"kind":"natMul", "left":{"kind":"project", "path":[]}, "right":{"kind":"project", "path":[]}}),
        json!({"kind":"sum", "items":{"kind":"project", "path":[]}, "expression":{"kind":"project", "path":["description"]}}),
    ] {
        let mut spec = source.clone();
        spec["form"]["children"][1]["expression"] = expression;
        spec["form"] =
            json!({"kind":"visibleWhen", "condition":boolean(false), "body":spec["form"].take()});
        assert!(Engine::parse(&spec.to_string()).is_err());
    }
}

#[test]
fn computed_values_use_item_and_constructor_scope() {
    let spec: Value = serde_json::from_str(include_str!("../../tests/invoice.json")).unwrap();
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    assert_eq!(e.shown(&e.fields()[3]), "100");
    e.selected = 1;
    edit(&mut e, "2");
    assert_eq!(e.shown(&e.fields()[3]), "200");
    let mut spec = shapes_spec();
    spec["value"] = json!({"tag":"circle", "value":"7"});
    spec["form"]["branches"]["circle"] = json!({"kind":"stack", "children":[spec["form"]["branches"]["circle"], {"kind":"computed", "label":"Radius copy", "type":{"kind":"natural"},
        "expression":{"kind":"project", "path":[]}}]});
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    assert_eq!(e.shown(&e.fields()[2]), "7");
    e.selected = 1;
    edit(&mut e, "9");
    assert_eq!(e.shown(&e.fields()[2]), "9");
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

#[test]
fn date_validation_matches_lean_and_rejects_invalid_initial_values() {
    let cases: Value = serde_json::from_str(include_str!("../../tests/dates.json")).unwrap();
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/booking.json")).unwrap();
    for value in cases["valid"].as_array().unwrap() {
        assert_eq!(
            date(value.as_str().unwrap()).unwrap().to_string(),
            value.as_str().unwrap()
        );
        spec["value"]["startDate"] = value.clone();
        assert!(Engine::parse(&spec.to_string()).is_ok());
    }
    for value in cases["invalid"].as_array().unwrap() {
        assert!(date(value.as_str().unwrap()).is_none());
        spec["value"]["startDate"] = value.clone();
        assert!(Engine::parse(&spec.to_string()).is_err());
    }
}

#[test]
fn date_editor_and_comparisons_preserve_calendar_validity() {
    let mut e = Engine::parse(include_str!("../../tests/booking.json")).unwrap();
    edit(&mut e, "2023-02-29");
    assert!(e
        .editor
        .as_ref()
        .unwrap()
        .error
        .as_ref()
        .unwrap()
        .contains("YYYY-MM-DD"));
    assert_eq!(e.spec.value["startDate"], "2028-02-28");
    keys(&mut e, &[Key::Clear]);
    text(&mut e, "2028-02-29");
    keys(&mut e, &[Key::Enter]);
    assert!(e.editor.is_none());
    assert!(e.errors().is_empty());
    e.selected = 1;
    edit(&mut e, "2028-02-28");
    assert_eq!(e.errors().len(), 1);
    assert!(e.step(Key::Character('q')));
    edit(&mut e, "2028-02-29");
    assert!(e.errors().is_empty());
    assert!(!e.step(Key::Character('q')));
    assert_eq!(
        serde_json::from_str::<Value>(&e.result()).unwrap(),
        json!({"startDate":"2028-02-29", "endDate":"2028-02-29"})
    );
}

#[test]
fn date_expressions_and_widgets_are_type_checked() {
    let source: Value = serde_json::from_str(include_str!("../../tests/booking.json")).unwrap();
    let mut spec = source.clone();
    spec["form"]["children"][0]["widget"] = json!("textInput");
    assert!(Engine::parse(&spec.to_string()).is_err());
    let mut spec = source.clone();
    spec["constraints"][0]["condition"]["left"] =
        json!({"kind":"value", "type":{"kind":"text"}, "value":"2028-02-28"});
    assert!(Engine::parse(&spec.to_string()).is_err());
    spec["constraints"][0]["condition"]["left"] =
        json!({"kind":"value", "type":{"kind":"date"}, "value":"2028-02-30"});
    assert!(Engine::parse(&spec.to_string()).is_err());
    let mut spec = source;
    spec["form"] = json!({"kind":"stack", "children":[spec["form"], {"kind":"computed", "label":"Start copy", "type":{"kind":"date"},
        "expression":{"kind":"project", "path":["startDate"]}}]});
    let e = Engine::parse(&spec.to_string()).unwrap();
    assert_eq!(e.shown(e.fields().last().unwrap()), "2028-02-28");
}

#[test]
fn booking_date_range_includes_endpoints_and_blocks_outside_dates() {
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/booking.json")).unwrap();
    for endpoint in ["2028-01-01", "2028-12-31"] {
        spec["value"] = json!({"startDate":endpoint, "endDate":endpoint});
        let e = Engine::parse(&spec.to_string()).unwrap();
        assert!(e.errors().is_empty());
    }
    let mut e = Engine::parse(include_str!("../../tests/booking.json")).unwrap();
    e.selected = 1;
    edit(&mut e, "2029-01-01");
    assert_eq!(e.errors().len(), 1);
    assert!(e.errors()[0].contains("between 2028-01-01 and 2028-12-31"));
    assert!(e.step(Key::Character('q')));
    edit(&mut e, "2028-12-31");
    e.selected = 0;
    edit(&mut e, "2027-12-31");
    assert_eq!(e.errors().len(), 1);
    assert!(e.step(Key::Character('q')));
    edit(&mut e, "2028-01-01");
    assert!(!e.step(Key::Character('q')));
}

#[test]
fn date_picker_modes_navigation_and_text_stay_in_sync() {
    let mut e = Engine::parse(include_str!("../../tests/booking.json")).unwrap();
    let original = e.spec.value.clone();
    keys(&mut e, &[Key::Enter, Key::Character('l')]);
    assert_eq!(e.editor.as_ref().unwrap().text, "2028-02-29");
    keys(&mut e, &[Key::Character('j')]);
    assert_eq!(e.editor.as_ref().unwrap().text, "2028-03-07");
    keys(&mut e, &[Key::Character('k'), Key::Character('h')]);
    assert_eq!(e.editor.as_ref().unwrap().text, "2028-02-28");
    keys(&mut e, &[Key::Character('9'), Key::Clear, Key::Backspace]);
    assert_eq!(e.editor.as_ref().unwrap().text, "2028-02-28");
    keys(&mut e, &[Key::Character('i'), Key::Clear]);
    text(&mut e, "2028-01-31");
    assert_eq!(e.editor.as_ref().unwrap().calendar, date("2028-01-31"));
    keys(&mut e, &[Key::Character('h')]);
    assert_eq!(e.editor.as_ref().unwrap().text, "2028-01-31h");
    keys(&mut e, &[Key::Backspace, Key::Escape, Key::PageDown]);
    assert_eq!(e.editor.as_ref().unwrap().text, "2028-02-29");
    keys(&mut e, &[Key::PageUp]);
    assert_eq!(e.editor.as_ref().unwrap().text, "2028-01-29");
    assert_eq!(e.spec.value, original);
    keys(&mut e, &[Key::Escape]);
    assert_eq!(e.spec.value, original);
    keys(&mut e, &[Key::Enter, Key::Right, Key::Enter]);
    assert!(e.editor.as_ref().unwrap().date_input);
    assert_eq!(e.spec.value, original);
    keys(&mut e, &[Key::Enter]);
    assert_eq!(e.spec.value["startDate"], "2028-02-29");
}

#[test]
fn date_picker_handles_invalid_text_and_year_limits() {
    let mut e = Engine::parse(include_str!("../../tests/booking.json")).unwrap();
    keys(&mut e, &[Key::Enter, Key::Enter, Key::Clear]);
    text(&mut e, "2028-02-30");
    keys(&mut e, &[Key::Enter]);
    assert!(e.editor.as_ref().unwrap().error.is_some());
    assert_eq!(e.editor.as_ref().unwrap().calendar, date("2028-02-28"));
    keys(&mut e, &[Key::Escape, Key::Right]);
    assert_eq!(e.editor.as_ref().unwrap().text, "2028-02-29");
    assert!(e.editor.as_ref().unwrap().error.is_none());
    keys(&mut e, &[Key::Character('i'), Key::Clear]);
    text(&mut e, "0001-01-01");
    keys(
        &mut e,
        &[
            Key::Escape,
            Key::Character('h'),
            Key::Character('k'),
            Key::PageUp,
        ],
    );
    assert_eq!(e.editor.as_ref().unwrap().text, "0001-01-01");
    keys(&mut e, &[Key::Character('i'), Key::Clear]);
    text(&mut e, "9999-12-31");
    keys(
        &mut e,
        &[
            Key::Escape,
            Key::Character('l'),
            Key::Character('j'),
            Key::PageDown,
        ],
    );
    assert_eq!(e.editor.as_ref().unwrap().text, "9999-12-31");
}

fn report() -> Engine {
    Engine::parse(include_str!("../../tests/report.json")).unwrap()
}

#[test]
fn report_filters_refresh_summary_and_rows_without_changing_source_results() {
    let mut engine = report();
    let source = engine.spec.value["results"].clone();
    let (fields, tables) = engine.content();
    assert_eq!(engine.shown(fields.last().unwrap()), "2/4 passed");
    assert_eq!(tables[0].columns, ["Test", "Provider", "Result"]);
    assert_eq!(tables[0].rows[0], ["Alpha", "Vertex", "PASS"]);
    keys(&mut engine, &[Key::Enter, Key::Down, Key::Enter]);
    assert_eq!(engine.content().1[0].rows.len(), 2);
    assert_eq!(engine.shown(engine.fields().last().unwrap()), "1/2 passed");
    keys(&mut engine, &[Key::Down, Key::Character(' ')]);
    assert_eq!(
        engine.content().1[0].rows,
        [vec!["Zulu", "Bedrock", "FAIL"]]
    );
    assert_eq!(engine.shown(engine.fields().last().unwrap()), "1/2 passed");
    assert_eq!(engine.spec.value["results"], source);
    assert!(!engine.step(Key::Character('q')));
    let result: Value = serde_json::from_str(&engine.result()).unwrap();
    assert_eq!(result["filters"], json!({"provider":1,"failuresOnly":true}));
}

#[test]
fn report_sort_selection_is_live_and_stable() {
    let mut engine = report();
    keys(
        &mut engine,
        &[Key::Down, Key::Down, Key::Enter, Key::Down, Key::Enter],
    );
    let names = |engine: &Engine| {
        engine.content().1[0]
            .rows
            .iter()
            .map(|row| row[0].clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(names(&engine), ["Zulu", "Delta", "Beta", "Alpha"]);
    keys(&mut engine, &[Key::Enter, Key::Down, Key::Enter]);
    assert_eq!(names(&engine), ["Zulu", "Beta", "Alpha", "Delta"]);
    assert_eq!(engine.shown(engine.fields().last().unwrap()), "2/4 passed");
}

#[test]
fn report_empty_results_keep_the_summary_denominator() {
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/report.json")).unwrap();
    for result in spec["value"]["results"].as_array_mut().unwrap() {
        result["passed"] = json!(true);
    }
    let mut engine = Engine::parse(&spec.to_string()).unwrap();
    keys(&mut engine, &[Key::Down, Key::Character(' ')]);
    assert!(engine.content().1[0].rows.is_empty());
    assert_eq!(engine.shown(engine.fields().last().unwrap()), "4/4 passed");
}

#[test]
fn report_weakened_by_lean_preserves_siblings_and_resolves_queries_locally() {
    let mut engine = Engine::parse(include_str!("../../tests/weakened-report.json")).unwrap();
    keys(
        &mut engine,
        &[
            Key::Enter,
            Key::Down,
            Key::Enter,
            Key::Down,
            Key::Character(' '),
        ],
    );
    assert_eq!(
        engine.content().1[0].rows,
        [vec!["Zulu", "Bedrock", "FAIL"]]
    );
    assert_eq!(engine.spec.value["title"], "Keep this title");
}

#[test]
fn report_protocol_rejects_invalid_bindings_and_queries() {
    let spec: Value = serde_json::from_str(include_str!("../../tests/report.json")).unwrap();
    let mut invalid = spec.clone();
    invalid["form"]["children"][0]["children"][0]["path"] = json!(["missing"]);
    assert!(Engine::parse(&invalid.to_string()).is_err());
    let mut invalid = spec.clone();
    invalid["form"]["children"][0]["children"][0]["schema"] = json!({"kind":"boolean"});
    assert!(Engine::parse(&invalid.to_string()).is_err());
    let mut invalid = spec.clone();
    invalid["form"]["children"][3]["rows"]["branches"]
        .as_array_mut()
        .unwrap()
        .pop();
    assert!(Engine::parse(&invalid.to_string()).is_err());
    let mut invalid = spec.clone();
    invalid["form"]["children"][3]["columns"][0]["expression"] =
        json!({"kind":"value","type":{"kind":"natural"},"value":"12"});
    assert!(Engine::parse(&invalid.to_string()).is_err());
    for expression in [
        json!({"kind":"filter","items":{"kind":"project","path":["results"]},
            "predicate":{"kind":"project","path":["name"]}}),
        json!({"kind":"sortBy","items":{"kind":"project","path":["results"]},
            "key":{"kind":"project","path":["passed"]},"descending":false}),
    ] {
        let mut invalid = spec.clone();
        invalid["form"]["children"][3]["rows"] = expression;
        assert!(Engine::parse(&invalid.to_string()).is_err());
    }
}

fn basket() -> Engine {
    Engine::parse(include_str!("../../tests/basket.json")).unwrap()
}
fn select_title(engine: &mut Engine, title: &str) {
    engine.selected = engine.fields().iter().position(|field| field.title == title).unwrap();
}
fn choose_title(engine: &mut Engine, title: &str, option: usize) {
    select_title(engine, title);
    engine.step(Key::Enter);
    // Start at the first option, regardless of the current choice.
    for _ in 0..10 { engine.step(Key::Up); }
    for _ in 0..option { engine.step(Key::Down); }
    engine.step(Key::Enter);
}
fn basket_total(engine: &Engine) -> String {
    engine.shown(&engine.fields()[0])
}
fn catalogue_names(engine: &Engine) -> Vec<String> {
    engine.content().1[0].rows.iter().map(|row| row[0].clone()).collect()
}

#[test]
fn basket_filters_sort_and_search_preserve_items_and_total() {
    let mut engine = basket();
    let items = engine.spec.value["items"].clone();
    assert_eq!(catalogue_names(&engine), ["Backpack", "Mug", "Notebook", "Pen", "Water bottle"]);
    choose_title(&mut engine, "Sort", 1);
    assert_eq!(catalogue_names(&engine), ["Pen", "Notebook", "Mug", "Water bottle", "Backpack"]);
    choose_title(&mut engine, "Sort", 2);
    assert_eq!(catalogue_names(&engine), ["Backpack", "Water bottle", "Mug", "Notebook", "Pen"]);
    choose_title(&mut engine, "Category", 1);
    assert_eq!(catalogue_names(&engine), ["Notebook", "Pen"]);
    select_title(&mut engine, "Search");
    edit(&mut engine, "PEN");
    assert_eq!(catalogue_names(&engine), ["Pen"]);
    edit(&mut engine, "no match");
    assert!(catalogue_names(&engine).is_empty());
    assert_eq!(basket_total(&engine), "Basket total: EUR 16");
    assert_eq!(engine.spec.value["items"], items);
    edit(&mut engine, "");
    choose_title(&mut engine, "Category", 0);
    choose_title(&mut engine, "Price limit", 1);
    assert_eq!(catalogue_names(&engine), ["Notebook", "Pen"]);
}

#[test]
fn basket_add_edit_remove_and_switch_pages_keep_current_state() {
    let mut engine = basket();
    choose_title(&mut engine, "Product to add", 2); // Mug, EUR 12
    select_title(&mut engine, "Add selected product");
    engine.step(Key::Enter);
    assert_eq!(basket_total(&engine), "Basket total: EUR 28");
    assert_eq!(engine.spec.value["items"].as_array().unwrap().len(), 3);
    engine.step(Key::Enter);
    assert_eq!(basket_total(&engine), "Basket total: EUR 40");
    choose_title(&mut engine, "Page", 1);
    assert!(!engine.fields().iter().any(|field| field.title == "Search"));
    select_title(&mut engine, "Quantity");
    edit(&mut engine, "4");
    assert_eq!(basket_total(&engine), "Basket total: EUR 50");
    assert_eq!(engine.content().1[0].rows[0], ["Notebook", "4", "20"]);
    for _ in 0..4 {
        select_title(&mut engine, "− Remove item");
        engine.step(Key::Enter);
    }
    assert_eq!(basket_total(&engine), "Basket total: EUR 0");
    assert!(engine.content().1[0].rows.is_empty());
    choose_title(&mut engine, "Page", 0);
    select_title(&mut engine, "Add selected product");
    engine.step(Key::Enter);
    assert_eq!(basket_total(&engine), "Basket total: EUR 12");
    assert!(!engine.step(Key::Character('q')));
    let result: Value = serde_json::from_str(&engine.result()).unwrap();
    assert_eq!(result["items"], json!([{"product":2,"quantity":"1"}]));
}

#[test]
fn shopping_operators_reject_invalid_types() {
    let schema = basket().spec.schema;
    let catalogue = json!({"kind":"value","type":{"kind":"list","element":{"kind":"natural"}},"value":["2","12"]});
    let self_key = json!({"kind":"project","path":[]});
    for expr in [
        json!({"kind":"search","items":catalogue,"key":self_key,"query":{"kind":"value","type":{"kind":"text"},"value":"2"}}),
        json!({"kind":"sortNatBy","items":{"kind":"value","type":{"kind":"list","element":{"kind":"text"}},"value":["a"]},"key":self_key,"descending":false}),
    ] {
        assert!(serde_json::from_value::<Expr>(expr).unwrap().ty(&schema).is_err());
    }
    let invalid = json!({"kind":"appendItemButton","label":"Bad","path":["items"],
        "value":{"kind":"value","type":{"kind":"text"},"value":"not an item"}});
    assert!(serde_json::from_value::<Component>(invalid).unwrap().validate(&schema).is_err());
}

#[test]
fn shopping_search_and_numeric_sort_match_lean_and_preserve_precision() {
    let expr: Expr = serde_json::from_value(json!({"kind":"sortNatBy",
        "items":{"kind":"value","type":{"kind":"list","element":{"kind":"natural"}},
        "value":["10000000000000000000000000000000000000000","12","2"]},
        "key":{"kind":"project","path":[]},"descending":false})).unwrap();
    assert_eq!(expr.eval(&Value::Null), json!(["2","12","10000000000000000000000000000000000000000"]));
    let search: Expr = serde_json::from_value(json!({"kind":"search",
        "items":{"kind":"value","type":{"kind":"list","element":{"kind":"text"}},"value":["Notebook","PEN","é"]},
        "key":{"kind":"project","path":[]},
        "query":{"kind":"value","type":{"kind":"text"},"value":"pen"}})).unwrap();
    assert_eq!(search.eval(&Value::Null), json!(["PEN"]));
}

#[test]
fn bound_field_reads_outer_context_and_only_writes_its_target() {
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/report.json")).unwrap();
    let editor = spec["form"]["children"][1].clone();
    spec["form"] = json!({"kind":"visibleWhen",
        "condition":{"kind":"project","path":["filters","failuresOnly"]},
        "body":editor});
    let engine = Engine::parse(&spec.to_string()).unwrap();
    assert!(engine.fields().is_empty());
    spec["value"]["filters"]["failuresOnly"] = json!(true);
    let mut engine = Engine::parse(&spec.to_string()).unwrap();
    let results = engine.spec.value["results"].clone();
    assert_eq!(engine.fields().len(), 1);
    keys(&mut engine, &[Key::Enter, Key::Down, Key::Enter]);
    assert_eq!(engine.spec.value["sort"], json!(1));
    assert_eq!(engine.spec.value["filters"]["failuresOnly"], json!(true));
    assert_eq!(engine.spec.value["results"], results);
    spec["form"]["body"]["path"] = Value::Null;
    assert!(Engine::parse(&spec.to_string()).is_err());
}

#[test]
fn basket_weakened_by_lean_preserves_outer_siblings() {
    let mut engine = Engine::parse(include_str!("../../tests/weakened-basket.json")).unwrap();
    choose_title(&mut engine, "Product to add", 2);
    select_title(&mut engine, "Add selected product");
    engine.step(Key::Enter);
    assert_eq!(basket_total(&engine), "Basket total: EUR 28");
    assert_eq!(engine.spec.value["title"], json!("Keep this title"));
    assert_eq!(engine.spec.value["content"]["items"].as_array().unwrap().len(), 3);
    choose_title(&mut engine, "Page", 1);
    select_title(&mut engine, "Quantity");
    edit(&mut engine, "4");
    assert_eq!(engine.content().1[0].rows[0], ["Notebook", "4", "20"]);
    assert_eq!(basket_total(&engine), "Basket total: EUR 38");
    assert_eq!(engine.spec.value["title"], json!("Keep this title"));
}

#[test]
fn components_inside_lists_and_sums_use_local_state() {
    let numbers = json!({"kind":"list", "element":{"kind":"natural"}});
    let body = json!({"kind":"stack", "children":[
        {"kind":"table", "rows":{"kind":"project","path":[]},
         "columns":[{"label":"Number", "expression":{"kind":"natToText",
             "operand":{"kind":"project","path":[]}}}]},
        {"kind":"appendItemButton", "label":"Append seven", "path":[],
         "value":{"kind":"value","type":{"kind":"natural"},"value":"7"}}
    ]});
    let list_schema = json!({"kind":"list","element":numbers});
    let sum_schema = json!({"kind":"sum","constructors":[{"name":"numbers","type":numbers}]});
    let cases = [
        (list_schema.clone(), json!([["1"],["2"]]),
         json!({"kind":"list","path":[],"schema":list_schema,"label":"Groups",
             "item":body,"defaultItem":[]}), json!([["1","7"],["2"]])),
        (sum_schema.clone(), json!({"tag":"numbers","value":["1"]}),
         json!({"kind":"sum","path":[],"schema":sum_schema,"label":"Choice",
             "branches":{"numbers":body},"defaults":{"numbers":[]}}),
         json!({"tag":"numbers","value":["1","7"]})),
    ];
    for (schema, value, form, expected) in cases {
        let spec = json!({"version":4,"schema":schema,"value":value,"constraints":[],"form":form});
        let mut engine = Engine::parse(&spec.to_string()).unwrap();
        assert_eq!(engine.content().1[0].rows, vec![vec!["1"]]);
        select_title(&mut engine, "Append seven");
        engine.step(Key::Enter);
        assert_eq!(engine.spec.value, expected);
        assert_eq!(engine.content().1[0].rows, vec![vec!["1"], vec!["7"]]);
        if engine.content().1.len() == 2 {
            assert_eq!(engine.content().1[1].rows, vec![vec!["2"]]);
        }
        let mut disabled = spec;
        disabled["form"] = json!({"kind":"disabledWhen",
            "condition":{"kind":"value","type":{"kind":"boolean"},"value":true},
            "body":disabled["form"]});
        let mut engine = Engine::parse(&disabled.to_string()).unwrap();
        select_title(&mut engine, "Append seven");
        assert!(engine.fields()[engine.selected].presentation.disabled);
        engine.step(Key::Enter);
        assert_eq!(engine.spec.value, value);
    }
}

#[test]
fn typed_natural_actions_update_live_values_and_preserve_local_scope() {
    for source in [include_str!("../../tests/basket.json"), include_str!("../../tests/weakened-basket.json")] {
        let mut engine = Engine::parse(source).unwrap();
        choose_title(&mut engine, "Page", 1);
        let before = engine.spec.value.clone();
        select_title(&mut engine, "+1");
        keys(&mut engine, &[Key::Enter, Key::Enter]);
        assert_eq!(engine.content().1[0].rows[0], ["Notebook", "4", "20"]);
        assert_eq!(basket_total(&engine), "Basket total: EUR 26");
        select_title(&mut engine, "−1");
        keys(&mut engine, &[Key::Enter]);
        assert_eq!(engine.content().1[0].rows[0][1], "3");
        select_title(&mut engine, "Reset quantity");
        keys(&mut engine, &[Key::Enter]);
        select_title(&mut engine, "−1");
        keys(&mut engine, &[Key::Enter]);
        assert_eq!(engine.content().1[0].rows[0][1], "0");
        select_title(&mut engine, "Quantity");
        edit(&mut engine, &"9".repeat(80));
        select_title(&mut engine, "+1");
        keys(&mut engine, &[Key::Enter]);
        assert_eq!(engine.content().1[0].rows[0][1], format!("1{}", "0".repeat(80)));
        select_title(&mut engine, "−1");
        keys(&mut engine, &[Key::Enter]);
        assert_eq!(engine.content().1[0].rows[0][1], "9".repeat(80));
        assert_eq!(engine.content().1[0].rows[1], ["Pen", "3", "6"]);
        assert_eq!(engine.spec.value["title"], before["title"]);
    }
}

#[test]
fn typed_actions_validate_paths_and_replacements_and_respect_disabled() {
    let mut spec = json!({"version":4, "schema":{"kind":"natural"}, "value":"4", "constraints":[],
        "form":{"kind":"button","label":"Set","action":{"kind":"set","path":[],
            "value":{"kind":"project","path":[]}}}});
    let mut engine = Engine::parse(&spec.to_string()).unwrap();
    engine.step(Key::Enter);
    assert_eq!(engine.spec.value, json!("4"));
    spec["form"]["action"]["value"] = json!({"kind":"value","type":{"kind":"natural"},"value":"7"});
    let mut engine = Engine::parse(&spec.to_string()).unwrap();
    engine.step(Key::Enter);
    assert_eq!(engine.spec.value, json!("7"));
    let mut disabled = spec.clone();
    disabled["form"] = json!({"kind":"disabledWhen",
        "condition":{"kind":"value","type":{"kind":"boolean"},"value":true},"body":spec["form"]});
    let mut engine = Engine::parse(&disabled.to_string()).unwrap();
    engine.step(Key::Enter);
    assert_eq!(engine.spec.value, json!("4"));
    spec["form"]["action"]["value"] = json!({"kind":"value","type":{"kind":"text"},"value":"oops"});
    assert!(Engine::parse(&spec.to_string()).is_err());
    for kind in ["increment", "decrement"] {
        spec["form"]["action"] = json!({"kind":kind,"path":["missing"]});
        assert!(Engine::parse(&spec.to_string()).is_err());
        spec["schema"] = json!({"kind":"text"});
        spec["value"] = json!("text");
        spec["form"]["action"] = json!({"kind":kind,"path":[]});
        assert!(Engine::parse(&spec.to_string()).is_err());
    }
}

#[test]
fn expression_actions_support_open_definitions_and_editor_arguments() {
    let source: Value = serde_json::from_str(include_str!("../../tests/counter.json")).unwrap();
    let mut engine = Engine::parse(&source.to_string()).unwrap();
    select_title(&mut engine, "+1");
    engine.step(Key::Enter);
    select_title(&mut engine, "+5");
    engine.step(Key::Enter);
    assert_eq!(engine.spec.value, json!("6"));
    select_title(&mut engine, "Value");
    edit(&mut engine, "0");
    select_title(&mut engine, "−1");
    engine.step(Key::Enter);
    assert_eq!(engine.spec.value, json!("0"));
    select_title(&mut engine, "Value");
    edit(&mut engine, &"9".repeat(80));
    select_title(&mut engine, "+1");
    engine.step(Key::Enter);
    assert_eq!(engine.spec.value, json!(format!("1{}", "0".repeat(80))));

    // A new action needs only an expression, with access to current and argument.
    let mut spec = source.clone();
    spec["value"] = json!("5");
    spec["form"]["actions"] = json!([{"id":"addAmount","label":"Add amount","kind":"editor",
        "widget":"naturalInput", "body":{"kind":"natAdd",
            "left":{"kind":"project","path":["current"]},
            "right":{"kind":"project","path":["argument"]}}}]);
    let mut engine = Engine::parse(&spec.to_string()).unwrap();
    edit(&mut engine, "3");
    assert_eq!(engine.spec.value, json!("8"));
    edit(&mut engine, "2");
    assert_eq!(engine.spec.value, json!("10"));
    edit(&mut engine, "-1");
    assert!(engine.editor.as_ref().unwrap().error.is_some());
    assert_eq!(engine.spec.value, json!("10"));

    // The same widget operates on each list item's local state.
    let natural = json!({"kind":"natural"});
    let list = json!({"kind":"list","element":natural});
    let nested = json!({"version":4,"schema":list,"value":["5","20"],"constraints":[],
        "form":{"kind":"list","path":[],"schema":list,"label":"Numbers",
            "item":spec["form"],"defaultItem":"0"}});
    let mut engine = Engine::parse(&nested.to_string()).unwrap();
    select_title(&mut engine, "Add amount");
    edit(&mut engine, "3");
    assert_eq!(engine.spec.value, json!(["8","20"]));

    let mut disabled = source.clone();
    disabled["version"] = json!(4);
    disabled["form"] = json!({"kind":"disabledWhen",
        "condition":{"kind":"value","type":{"kind":"boolean"},"value":true},"body":source["form"]});
    let mut engine = Engine::parse(&disabled.to_string()).unwrap();
    engine.step(Key::Enter);
    assert_eq!(engine.spec.value, json!("0"));
    select_title(&mut engine, "Value");
    engine.step(Key::Enter);
    assert!(engine.editor.is_none());
}

#[test]
fn widget_action_specs_reject_duplicate_ids_and_wrong_types() {
    let source: Value = serde_json::from_str(include_str!("../../tests/counter.json")).unwrap();
    for invalid in [
        json!({"id":"bad","label":"Bad","kind":"button", "body":{"kind":"project","path":["argument"]}}),
        json!({"id":"bad","label":"Bad","kind":"button", "body":{"kind":"value","type":{"kind":"text"},"value":"oops"}}),
        json!({"id":"bad","label":"Bad","kind":"editor","widget":"textInput", "body":{"kind":"project","path":["argument"]}}),
        json!({"id":"bad","label":"Bad","kind":"button", "body":{"kind":"natSub", "left":{"kind":"value","type":{"kind":"text"},"value":"oops"}, "right":{"kind":"project","path":[]}}}),
    ] {
        let mut spec = source.clone();
        spec["form"]["actions"] = json!([invalid]);
        assert!(Engine::parse(&spec.to_string()).is_err());
    }
    let mut spec = source.clone();
    spec["form"]["actions"][1]["id"] = spec["form"]["actions"][0]["id"].clone();
    assert!(Engine::parse(&spec.to_string()).is_err());
    spec["form"]["actions"] = json!([]);
    assert!(Engine::parse(&spec.to_string()).unwrap().fields().is_empty());
}

#[test]
fn empty_action_ids_are_recorded_and_must_be_unique() {
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/counter.json")).unwrap();
    spec["form"]["actions"][0]["id"] = json!("");
    let mut engine = Engine::parse(&spec.to_string()).unwrap();
    engine.step(Key::Enter);
    engine.step(Key::Character('q'));
    assert_eq!(serde_json::from_str::<Value>(&engine.result()).unwrap(),
        json!({"value":"1", "actions":[{"target":[],"action":""}]}));

    spec["form"]["actions"][1]["id"] = json!("");
    assert!(Engine::parse(&spec.to_string()).is_err());
}

#[test]
fn root_widget_returns_only_accepted_invocations() {
    let source = include_str!("../../tests/counter.json");
    let mut engine = Engine::parse(source).unwrap();
    assert!(!engine.step(Key::Character('q')));
    assert_eq!(serde_json::from_str::<Value>(&engine.result()).unwrap(),
        json!({"value":"0", "actions":[]}));

    let mut engine = Engine::parse(source).unwrap();
    keys(&mut engine, &[Key::Enter, Key::Enter]);
    select_title(&mut engine, "Value");
    edit(&mut engine, "bad");
    assert!(engine.editor.as_ref().unwrap().error.is_some());
    engine.step(Key::Escape);
    keys(&mut engine, &[Key::Enter, Key::Clear, Key::Character('9'), Key::Escape]);
    edit(&mut engine, "42");
    select_title(&mut engine, "−1");
    engine.step(Key::Enter);
    assert!(!engine.step(Key::Character('q')));
    assert_eq!(serde_json::from_str::<Value>(&engine.result()).unwrap(), json!({
        "value":"41", "actions":[{"target":[],"action":"plusOne"}, {"target":[],"action":"plusOne"},
            {"target":[],"action":"replace", "argument":"42"}, {"target":[],"action":"minusOne"}]
    }));

    let mut engine = Engine::parse(source).unwrap();
    engine.step(Key::Enter);
    assert!(!engine.step(Key::Escape));
    assert_eq!(engine.result(), "null");
}

#[test]
fn root_editor_history_records_arguments_before_transformation() {
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/counter.json")).unwrap();
    spec["value"] = json!("5");
    spec["form"]["actions"] = json!([{"id":"add", "label":"Add", "kind":"editor",
        "widget":"naturalInput", "body":{"kind":"natAdd",
            "left":{"kind":"project","path":["current"]},
            "right":{"kind":"project","path":["argument"]}}}]);
    let mut engine = Engine::parse(&spec.to_string()).unwrap();
    edit(&mut engine, "3");
    engine.step(Key::Character('q'));
    assert_eq!(serde_json::from_str::<Value>(&engine.result()).unwrap(),
        json!({"value":"8", "actions":[{"target":[],"action":"add", "argument":"3"}]}));
}

#[test]
fn history_protocol_rejects_unsupported_forms() {
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/person.json")).unwrap();
    spec["version"] = json!(6);
    assert!(Engine::parse(&spec.to_string()).is_err());
}

#[test]
fn conditional_history_checks_current_state_and_preserves_targets() {
    let source: Value = serde_json::from_str(include_str!("../../tests/counter.json")).unwrap();
    for kind in ["visibleWhen", "disabledWhen"] {
        let mut spec = source.clone();
        let condition = if kind == "visibleWhen" {
            json!({"kind":"natLe","left":{"kind":"project","path":[]},
                "right":{"kind":"value","type":{"kind":"natural"},"value":"0"}})
        } else {
            json!({"kind":"natLe","left":{"kind":"value","type":{"kind":"natural"},"value":"1"},
                "right":{"kind":"project","path":[]}})
        };
        spec["form"] = json!({"kind":kind,"condition":condition,"body":source["form"]});
        let mut engine = Engine::parse(&spec.to_string()).unwrap();
        keys(&mut engine, &[Key::Enter, Key::Enter]);
        assert!(!engine.step(Key::Character('q')));
        assert_eq!(serde_json::from_str::<Value>(&engine.result()).unwrap(),
            json!({"value":"1","actions":[{"target":[],"action":"plusOne"}]}));

        spec["form"] = json!({"kind":"disabledWhen",
            "condition":{"kind":"value","type":{"kind":"boolean"},"value":false},
            "body":{"kind":"stack","childIds":["guarded","restore"],
                "children":[spec["form"],source["form"]]}});
        let mut engine = Engine::parse(&spec.to_string()).unwrap();
        engine.step(Key::Enter);
        engine.selected = engine.fields().iter().rposition(|field| field.title == "−1").unwrap();
        engine.step(Key::Enter);
        engine.selected = 0;
        engine.step(Key::Enter);
        assert!(!engine.step(Key::Character('q')));
        assert_eq!(serde_json::from_str::<Value>(&engine.result()).unwrap(), json!({
            "value":"1","actions":[
                {"target":["guarded"],"action":"plusOne"},
                {"target":["restore"],"action":"minusOne"},
                {"target":["guarded"],"action":"plusOne"}]}));
    }
}

#[test]
fn conditional_history_rejects_unsupported_children() {
    let source: Value = serde_json::from_str(include_str!("../../tests/person.json")).unwrap();
    for kind in ["visibleWhen", "disabledWhen"] {
        let mut spec = source.clone();
        spec["version"] = json!(6);
        spec["form"] = json!({"kind":kind,
            "condition":{"kind":"value","type":{"kind":"boolean"},"value":false},
            "body":source["form"]});
        assert!(Engine::parse(&spec.to_string()).is_err());
    }
}

#[test]
fn root_widget_records_each_editor_input_kind() {
    for (schema, widget, initial, argument) in [
        (json!({"kind":"boolean"}), "checkbox", json!(false), json!(true)),
        (json!({"kind":"enum","options":["A","B"]}), "select", json!(0), json!(1)),
        (json!({"kind":"text"}), "textInput", json!("old"), json!("new")),
        (json!({"kind":"date"}), "dateInput", json!("2028-02-28"), json!("2028-02-29")),
    ] {
        let spec = json!({"version":6,"schema":schema,"value":initial,"constraints":[],
            "form":{"kind":"actionWidget","path":[],"schema":schema,"label":"Editor",
                "actions":[{"id":"replace","label":"Value","kind":"editor","widget":widget,
                    "body":{"kind":"project","path":["argument"]}}]}});
        let mut engine = Engine::parse(&spec.to_string()).unwrap();
        match widget {
            "checkbox" => { engine.step(Key::Character(' ')); }
            "select" => keys(&mut engine, &[Key::Enter, Key::Down, Key::Enter]),
            _ => edit(&mut engine, argument.as_str().unwrap()),
        }
        assert!(!engine.step(Key::Character('q')));
        assert_eq!(serde_json::from_str::<Value>(&engine.result()).unwrap(),
            json!({"value":argument,"actions":[{"target":[],"action":"replace","argument":argument}]}));
    }
}

#[test]
fn stacked_widgets_record_distinct_targets_and_editor_arguments() {
    let mut engine = Engine::parse(include_str!("../../tests/counters.json")).unwrap();
    engine.step(Key::Enter);
    engine.selected = 5;
    engine.step(Key::Enter);
    engine.selected = 6;
    edit(&mut engine, "42");
    assert!(!engine.step(Key::Character('q')));
    assert_eq!(serde_json::from_str::<Value>(&engine.result()).unwrap(), json!({
        "value":{"left":"1","right":"42"},
        "actions":[{"target":["left"],"action":"plusOne"},
            {"target":["right"],"action":"plusFive"},
            {"target":["right"],"action":"replace","argument":"42"}]
    }));
}

#[test]
fn widget_targets_follow_child_ids_through_reordering_and_nesting() {
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/counters.json")).unwrap();
    spec["form"]["children"].as_array_mut().unwrap().reverse();
    spec["form"]["childIds"].as_array_mut().unwrap().reverse();
    let mut engine = Engine::parse(&spec.to_string()).unwrap();
    engine.step(Key::Enter);
    engine.step(Key::Character('q'));
    assert_eq!(serde_json::from_str::<Value>(&engine.result()).unwrap(), json!({
        "value":{"left":"0","right":"11"},
        "actions":[{"target":["right"],"action":"plusOne"}]
    }));
    spec["form"] = json!({"kind":"stack","childIds":["outer"],"children":[spec["form"]]});
    let mut engine = Engine::parse(&spec.to_string()).unwrap();
    engine.step(Key::Enter);
    engine.step(Key::Character('q'));
    assert_eq!(serde_json::from_str::<Value>(&engine.result()).unwrap()["actions"],
        json!([{"target":["outer","right"],"action":"plusOne"}]));
}

#[test]
fn history_stacks_reject_missing_duplicate_and_mismatched_ids() {
    let spec: Value = serde_json::from_str(include_str!("../../tests/counters.json")).unwrap();
    for ids in [json!(null), json!([]), json!(["left"]), json!(["same","same"])] {
        let mut malformed = spec.clone();
        malformed["form"]["childIds"] = ids;
        assert!(Engine::parse(&malformed.to_string()).is_err());
    }
    let mut malformed = spec.clone();
    malformed["form"].as_object_mut().unwrap().remove("childIds");
    assert!(Engine::parse(&malformed.to_string()).is_err());
    let mut mixed = spec;
    mixed["form"]["children"][1] = json!({"kind":"field","path":["right"],
        "schema":{"kind":"natural"},"label":"Right","widget":"naturalInput"});
    assert!(Engine::parse(&mixed.to_string()).is_err());
    mixed["version"] = json!(4);
    assert!(Engine::parse(&mixed.to_string()).is_ok());
}
