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
    let item = spec["form"]["body"]["item"].clone();
    spec["form"]["body"]["item"] = json!({"kind":"visibleWhen", "condition":{
        "kind":"natLe", "left":{"kind":"value", "type":{"kind":"natural"}, "value":"1"},
        "right":{"kind":"project", "path":["quantity"]}}, "body":item});
    let inner_schema = spec["schema"].clone();
    let inner_form = spec["form"].clone();
    let inner_value = spec["value"].clone();
    spec["schema"] = json!({"kind":"list", "element":inner_schema});
    spec["form"] = json!({"kind":"list", "label":"Invoices", "item":inner_form, "defaultItem":[]});
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
    spec["form"]["body"]["defaultItem"] = json!(false);
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
        (
            "/constraints/0/condition",
            json!({"kind":"project", "path":["home"]}),
        ),
        ("/constraints/2/condition/left/path", json!(["missing"])),
        ("/constraints/2/errorLocation", json!(["home", "home"])),
        ("/value/home", json!(-1)),
        ("/form/children/home/widget", json!("checkbox")),
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
fn disabling_choice_and_text_editing_still_work() {
    let mut e = person();
    assert_eq!(e.fields().len(), 5);
    assert!(e.fields()[3].presentation.disabled);
    keys(&mut e, &[Key::Down, Key::Down, Key::Character(' ')]);
    assert_eq!(e.fields().len(), 5);
    keys(&mut e, &[Key::Down]);
    edit(&mut e, "Elm Street");
    keys(&mut e, &[Key::Up, Key::Character(' ')]);
    assert_eq!(e.fields().len(), 5);
    assert!(e.fields()[3].presentation.disabled);
    assert_eq!(e.spec.value["address"]["street"], "Elm Street");
    keys(&mut e, &[Key::Down, Key::Enter]);
    assert!(e.editor.is_none());
    keys(&mut e, &[Key::Down, Key::Enter, Key::Down, Key::Escape]);
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
            "/form/branches/rectangle/children/width/widget",
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
        json!({"kind":"list","label":"Shapes","item":source["form"],"defaultItem":source["value"]});
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
    spec["form"] = json!({"kind":"sum", "label":"Shape",
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
    let root: Ty = serde_json::from_value(spec["schema"].clone()).unwrap();
    let dimension = json!({"kind":"cases", "type":{"kind":"natural"},
        "subject":{"kind":"project","path":[]},
        "branches":{"dot":{"kind":"value","type":{"kind":"natural"},"value":"0"},
                    "circle":{"kind":"project","path":[]}, "rectangle":{"kind":"project","path":["height"]}}});
    let expr: Expr = serde_json::from_value(dimension.clone()).unwrap();
    assert_eq!(expr.ty(&root).unwrap(), Ty::Natural);
    // Evaluating the rectangle branch on Dot would access a missing field.
    assert_eq!(expr.eval(&json!({"tag":"dot","value":{}})), "0");
    assert_eq!(
        expr.eval(&json!({"tag":"rectangle","value":{"width":"7","height":"2"}})),
        "2"
    );
    let condition: Expr = serde_json::from_value(json!({"kind":"natLe","left":dimension,
        "right":{"kind":"value","type":{"kind":"natural"},"value":"1"}}))
    .unwrap();
    assert_eq!(condition.ty(&root).unwrap(), Ty::Boolean);
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
            expr.ty(&root).unwrap(),
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
        assert!(expr.ty(&root).is_err(), "{path}");
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
    spec["form"]["children"]
        .as_object_mut()
        .unwrap()
        .remove("away");
    spec["form"]["children"]["wrong"] = source["form"]["children"]["away"].clone();
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
    let spec = json!({"version":2,"constraints":[],
        "schema":{"kind":"record","fields":[{"name":"tag","type":{"kind":"text"}},
            {"name":"value","type":{"kind":"natural"}}]},
        "form":{"kind":"group","label":"Record","displayOrder":["tag","value"],"children":{
            "tag":{"kind":"field","label":"Tag","widget":"textInput"},
            "value":{"kind":"field","label":"Value","widget":"naturalInput"}}},
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
    spec["form"]["displayOrder"] = json!(["away", "home"]);
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
    spec["form"]["body"]["item"]["body"]["displayOrder"] =
        json!(["unitPrice", "description", "quantity"]);
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    assert_eq!(e.fields()[0].title, "Unit price (cents)");
    edit(&mut e, "250");
    assert_eq!(e.spec.value[0]["unitPrice"], "250");
    e.selected = 5;
    keys(&mut e, &[Key::Enter]);
    assert_eq!(e.fields()[5].title, "Unit price (cents)");

    let mut spec = shapes_spec();
    spec["form"]["branches"]["rectangle"]["displayOrder"] = json!(["height", "width"]);
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
fn display_order_must_be_a_permutation_even_for_hidden_groups() {
    let source: Value = serde_json::from_str(include_str!("../../tests/thermostat.json")).unwrap();
    for order in [
        json!([]),
        json!(["home"]),
        json!(["home", "home"]),
        json!(["home", "unknown"]),
        json!(["home", "away", "extra"]),
        json!([0, 1]),
    ] {
        let mut spec = source.clone();
        spec["form"]["displayOrder"] = order;
        let body = spec["form"].clone();
        spec["form"] = json!({"kind":"visibleWhen", "condition":{"kind":"value", "type":{"kind":"boolean"}, "value":false}, "body":body});
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
    spec["form"]["children"]["name"] = disabled(
        json!({"kind":"project", "path":["subscribed"]}),
        spec["form"]["children"]["name"].take(),
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
    spec["form"]["children"]["name"]["condition"] = json!({"kind":"project", "path":["age"]});
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
    spec["form"]["body"]["item"] = disabled(condition, spec["form"]["body"]["item"].take());
    let e = Engine::parse(&spec.to_string()).unwrap();
    assert!(e.fields()[0..4].iter().all(|f| f.presentation.disabled));
    assert!(e.fields()[4..].iter().all(|f| !f.presentation.disabled));
}

#[test]
fn negation_rejects_non_boolean_operands() {
    let mut spec: Value = serde_json::from_str(include_str!("../../tests/person.json")).unwrap();
    spec["form"]["children"]["address"]["children"]["street"]["condition"]["operand"] =
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
        spec["form"]["expression"] = expression;
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
    spec["form"]["branches"]["circle"] = json!({"kind":"computed", "label":"Radius copy", "type":{"kind":"natural"},
        "expression":{"kind":"project", "path":[]}, "body":spec["form"]["branches"]["circle"].take()});
    let mut e = Engine::parse(&spec.to_string()).unwrap();
    assert_eq!(e.shown(&e.fields()[2]), "7");
    e.selected = 1;
    edit(&mut e, "9");
    assert_eq!(e.shown(&e.fields()[2]), "9");
}
