use super::*;
use ratatui::backend::TestBackend;

fn contents(terminal: &Terminal<TestBackend>) -> String {
    terminal
        .backend()
        .buffer()
        .content()
        .iter()
        .map(|cell| cell.symbol())
        .collect()
}

#[test]
fn table_scrolls_to_selection_and_shows_validation() {
    let labels: Vec<_> = (0..30).map(|i| format!("Person.Field{i}")).collect();
    let screen = Screen {
        errors: vec![],
        fields: labels
            .iter()
            .map(|label| Field {
                presentation: interpreter::Presentation::default(),
                label,
                value: "12",
                section: "",
                action: false,
            })
            .collect(),
        selected: 29,
        editor: Some(Editor {
            calendar: None,
            date_input: false,
            constructor: false,
            label: "Person.Field29".into(),
            text: "-1".into(),
            error: Some("Enter a non-negative whole number.".into()),
            choice: None,
            options: &[],
        }),
    };
    let mut terminal = Terminal::new(TestBackend::new(80, 24)).unwrap();
    let mut state = TableState::default();
    terminal
        .draw(|frame| render(frame, &screen, &mut state, Theme::FRAPPE))
        .unwrap();
    let text = contents(&terminal);
    assert!(text.contains("Person.Field29"));
    assert!(text.contains("Enter a non-negative whole number."));
    assert!(state.offset() > 0);
    assert!(terminal
        .backend()
        .buffer()
        .content()
        .iter()
        .any(|cell| cell.bg == Theme::FRAPPE.selection && cell.fg == Theme::FRAPPE.text));
}

#[test]
fn choice_editor_shows_selection_and_navigation() {
    let options = vec!["Home".into(), "Work".into(), "Other".into()];
    let screen = Screen {
        errors: vec![],
        fields: vec![Field {
            presentation: interpreter::Presentation::default(),
            label: "Address kind",
            value: "Home",
            section: "",
            action: false,
        }],
        selected: 0,
        editor: Some(Editor {
            calendar: None,
            date_input: false,
            constructor: false,
            label: "Address kind",
            text: "Home",
            error: None,
            choice: Some(1),
            options: &options,
        }),
    };
    for code in 0..=6 {
        let theme = Theme::from_code(code).unwrap();
        let mut terminal = Terminal::new(TestBackend::new(80, 24)).unwrap();
        terminal
            .draw(|frame| render(frame, &screen, &mut TableState::default(), theme))
            .unwrap();
        let text = contents(&terminal);
        for label in ["Home", "Work", "Other"] {
            assert!(text.contains(label));
        }
        assert!(text.contains("› Work"));
        assert!(text.contains("2 / 3"));
        assert!(text.contains("↑/↓ or j/k choose"));
        assert!(!text.contains("Backspace delete"));
        assert!(terminal
            .backend()
            .buffer()
            .content()
            .iter()
            .any(|cell| cell.symbol() == "W"
                && cell.fg == theme.text
                && cell.bg == theme.selection));
        assert_eq!(terminal.backend().buffer()[(0, 0)].bg, theme.base);
    }
}

#[test]
fn draft_validation_errors_are_visible_outside_the_editor() {
    let screen = Screen {
        fields: vec![Field {
            presentation: interpreter::Presentation::default(),
            label: "Thermostat.Away temperature (C)",
            value: "100",
            section: "",
            action: false,
        }],
        errors: vec![
            "Away temperature (C): Away temperature must not exceed home temperature.".into(),
        ],
        selected: 0,
        editor: None,
    };
    let mut terminal = Terminal::new(TestBackend::new(80, 24)).unwrap();
    terminal
        .draw(|frame| render(frame, &screen, &mut TableState::default(), Theme::FRAPPE))
        .unwrap();
    let text = contents(&terminal);
    assert!(text.contains("Resolve before submitting"));
    assert!(text.contains("Away temperature must not exceed home temperature."));
    assert!(text.contains("q submit"));
    assert!(text.contains("x cancel"));
}

#[test]
fn invoice_sections_actions_and_scrolling() {
    let mut engine = Engine::parse(include_str!("../tests/invoice.json")).unwrap();
    engine.selected = 5;
    engine.step(Key::Enter);
    let fields = engine.fields();
    let values: Vec<_> = fields.iter().map(|field| engine.shown(field)).collect();
    let mut screen = Screen {
        fields: fields
            .iter()
            .zip(&values)
            .map(|(field, value)| Field {
                presentation: field.presentation,
                label: &field.title,
                section: &field.section,
                action: field.action,
                value,
            })
            .collect(),
        selected: 0,
        errors: vec![],
        editor: None,
    };
    let mut terminal = Terminal::new(TestBackend::new(80, 24)).unwrap();
    let mut state = TableState::default();
    terminal
        .draw(|frame| render(frame, &screen, &mut state, Theme::FRAPPE))
        .unwrap();
    let text = contents(&terminal);
    for label in [
        "Invoice › Item 1",
        "Invoice › Item 2",
        "Description",
        "Quantity",
        "+ Add item",
        "− Remove item",
        "Ready to submit",
    ] {
        assert!(text.contains(label), "Missing {label}");
    }
    assert!(!text.contains("Invoice.1.Item.Description"));
    screen.selected = screen.fields.len() - 1;
    let mut small = Terminal::new(TestBackend::new(40, 14)).unwrap();
    small
        .draw(|frame| render(frame, &screen, &mut state, Theme::LATTE))
        .unwrap();
    let text = contents(&small);
    assert!(text.contains("+ Add item"));
    assert!(state.offset() > 0);
}

#[test]
fn narrow_terminal_and_wide_text_are_handled() {
    let screen = Screen {
        errors: vec![],
        fields: vec![],
        selected: 0,
        editor: None,
    };
    let mut terminal = Terminal::new(TestBackend::new(31, 10)).unwrap();
    terminal
        .draw(|frame| render(frame, &screen, &mut TableState::default(), Theme::FRAPPE))
        .unwrap();
    assert!(contents(&terminal).contains("Enlarge terminal"));
    assert_eq!(editor_tail("Ada界", 3), "a界");
    assert_eq!(clean("Ada\n\u{1b}"), "Ada  ");
}

#[test]
fn field_selection_leaves_heading_and_unused_width_unshaded() {
    let screen = Screen {
        fields: vec![Field {
            presentation: interpreter::Presentation::default(),
            label: "Description",
            value: "New item",
            section: "Invoice › Item 1",
            action: false,
        }],
        errors: vec![],
        selected: 0,
        editor: None,
    };
    for theme in [Theme::FRAPPE, Theme::LATTE] {
        let mut terminal = Terminal::new(TestBackend::new(100, 24)).unwrap();
        terminal
            .draw(|frame| render(frame, &screen, &mut TableState::default(), theme))
            .unwrap();
        let buffer = terminal.backend().buffer();
        let highlighted: Vec<_> = (0..24)
            .flat_map(|y| (0..100).map(move |x| (x, y)))
            .filter(|&(x, y)| buffer[(x, y)].bg == theme.selection)
            .collect();
        assert_eq!(highlighted.len(), " Description  New item ".len());
        let y = highlighted[0].1;
        assert!(highlighted.iter().all(|&(_, row)| row == y));
        assert_eq!(buffer[(1, y)].symbol(), "›");
        assert!((0..100).all(|x| buffer[(x, y - 1)].bg != theme.selection));
        assert_eq!(buffer[(90, y)].bg, theme.base);
    }
}

fn draw_engine(engine: &Engine, width: u16, height: u16, theme: Theme) -> String {
    let fields = engine.fields();
    let values: Vec<_> = fields.iter().map(|field| engine.shown(field)).collect();
    let screen = Screen {
        fields: fields
            .iter()
            .zip(&values)
            .map(|(field, value)| Field {
                presentation: field.presentation,
                label: &field.title,
                section: &field.section,
                action: field.action,
                value,
            })
            .collect(),
        errors: engine.errors(),
        selected: engine.selected,
        editor: engine.editor.as_ref().map(|editor| Editor {
            calendar: editor.calendar,
            date_input: editor.date_input,
            constructor: fields[engine.selected].presentation.constructor,
            label: &fields[engine.selected].title,
            text: &editor.text,
            error: editor.error.as_deref(),
            choice: editor.choice,
            options: &editor.options,
        }),
    };
    let mut terminal = Terminal::new(TestBackend::new(width, height)).unwrap();
    terminal
        .draw(|frame| render(frame, &screen, &mut TableState::default(), theme))
        .unwrap();
    terminal
        .backend()
        .buffer()
        .content()
        .chunks(width as usize)
        .map(|row| row.iter().map(|cell| cell.symbol()).collect::<String>())
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn sum_selector_groups_payload_and_explains_empty_constructors() {
    let mut spec: serde_json::Value =
        serde_json::from_str(include_str!("../tests/shapes.json")).unwrap();
    spec["value"] = serde_json::json!({"tag":"dot","value":{}});
    let mut engine = Engine::parse(&spec.to_string()).unwrap();
    for theme in [Theme::FRAPPE, Theme::LATTE] {
        let text = draw_engine(&engine, 80, 24, theme);
        assert!(text.contains("dot ▾"));
        assert!(text.contains("No details required"));
        assert!(text.contains("Enter choose"));
        assert_eq!(text.matches("Shape").count(), 2); // Page title and selector.
    }
    for (width, height) in [(32, 12), (40, 14)] {
        let text = draw_engine(&engine, width, height, Theme::FRAPPE);
        assert!(text.contains("dot ▾"));
        assert!(text.contains("No details"));
        assert!(text.contains("required"));
    }
    for key in [Key::Enter, Key::Down, Key::Down] {
        engine.step(key);
    }
    let text = draw_engine(&engine, 80, 24, Theme::FRAPPE);
    assert!(text.contains("› rectangle"));
    assert!(text.contains("Enter switch"));
    assert!(text.contains("Drafts kept"));
    engine.step(Key::Enter);
    let fields = engine.fields();
    assert_eq!(fields.len(), 3);
    assert_eq!(fields[1].presentation.depth, 1);
    assert_eq!(fields[0].section, fields[1].section);
    let text = draw_engine(&engine, 80, 24, Theme::FRAPPE);
    assert!(text.contains("rectangle ▾"));
    assert!(text.contains("│  Width"));
    assert!(text.contains("│  Height"));
    assert!(!text.contains("No details required"));
    assert!(!text.contains("Dimensions"));
}

#[test]
fn sum_validation_marks_selector_and_preserves_nested_grouping() {
    let source: serde_json::Value =
        serde_json::from_str(include_str!("../tests/shapes.json")).unwrap();
    let mut spec = source.clone();
    spec["value"] = serde_json::json!({"tag":"rectangle","value":{"width":"7","height":"0"}});
    let engine = Engine::parse(&spec.to_string()).unwrap();
    assert!(engine.fields()[0].presentation.invalid);
    let text = draw_engine(&engine, 80, 24, Theme::FRAPPE);
    assert!(text.contains("rectangle ▾ !"));
    assert!(text.contains("Size must be at least 1"));
    spec["schema"] = serde_json::json!({"kind":"sum","constructors":[{"name":"standard","type":source["schema"]}]});
    spec["form"] = serde_json::json!({"kind":"sum","label":"Order",
        "branches":{"standard":source["form"]},"defaults":{"standard":source["value"]}});
    spec["value"] = serde_json::json!({"tag":"standard","value":{"tag":"rectangle","value":{"width":"7","height":"1"}}});
    spec["constraints"] = serde_json::json!([]);
    let mut engine = Engine::parse(&spec.to_string()).unwrap();
    let fields = engine.fields();
    assert_eq!(
        fields
            .iter()
            .map(|field| field.presentation.depth)
            .collect::<Vec<_>>(),
        [0, 1, 2, 2]
    );
    assert_eq!(fields[1].section, "Order › Shape");
    assert_eq!(fields[2].section, fields[1].section);
    engine.selected = 3;
    let text = draw_engine(&engine, 40, 14, Theme::LATTE);
    assert!(text.contains("Height"));
    assert!(text.contains("4 / 4"));
}

#[test]
fn hidden_payload_is_distinguished_from_an_empty_constructor() {
    let mut spec: serde_json::Value =
        serde_json::from_str(include_str!("../tests/shapes.json")).unwrap();
    let body = spec["form"]["branches"]["rectangle"].clone();
    spec["form"]["branches"]["rectangle"] = serde_json::json!({"kind":"visibleWhen",
        "condition":{"kind":"value","type":{"kind":"boolean"},"value":false}, "body":body});
    spec["value"] = serde_json::json!({"tag":"rectangle","value":{"width":"7","height":"0"}});
    let engine = Engine::parse(&spec.to_string()).unwrap();
    let text = draw_engine(&engine, 80, 24, Theme::FRAPPE);
    assert!(text.contains("No fields to edit"));
    assert!(!text.contains("No details required"));
    assert!(text.contains("rectangle ▾ !"));
    assert!(text.contains("Size must be at least 1"));
}

#[test]
fn disabled_controls_show_values_without_edit_hints() {
    let mut spec: serde_json::Value =
        serde_json::from_str(include_str!("../tests/thermostat.json")).unwrap();
    spec["form"] = serde_json::json!({"kind":"disabledWhen", "condition":{"kind":"value", "type":{"kind":"boolean"}, "value":true}, "body":spec["form"].take()});
    let engine = interpreter::Engine::parse(&spec.to_string()).unwrap();
    let text = draw_engine(&engine, 100, 24, Theme::FRAPPE);
    assert!(text.contains("22 [disabled]"));
    assert!(text.contains("Disabled ·"));
    assert!(!text.contains("Enter edit"));
}

#[test]
fn computed_total_is_visible_with_read_only_hints() {
    let mut e = interpreter::Engine::parse(include_str!("../tests/invoice.json")).unwrap();
    e.selected = e.fields().len() - 1;
    let text = draw_engine(&e, 100, 24, Theme::FRAPPE);
    assert!(text.contains("Total (cents)"));
    assert!(text.contains("100 [computed]"));
    assert!(text.contains("Computed ·"));
    assert!(!text.contains("Enter edit"));
}

#[test]
fn hybrid_date_editor_shows_input_calendar_and_controls() {
    let mut e = Engine::parse(include_str!("../tests/booking.json")).unwrap();
    e.step(Key::Enter);
    e.step(Key::Right);
    for (width, height) in [(100, 24), (32, 12), (40, 16)] {
        let text = draw_engine(&e, width, height, Theme::FRAPPE);
        assert!(text.contains("2028-02-29"));
        assert!(text.contains("February 2028"));
        assert!(text.contains("Mo Tu We Th Fr Sa Su"));
        assert!(text.contains("29"));
        assert!(text.contains("i / Enter edit input"));
        assert!(text.contains("PgUp/PgDn month"));
    }
    e.step(Key::Character('i'));
    e.step(Key::Clear);
    let text = draw_engine(&e, 100, 24, Theme::LATTE);
    assert!(text.contains("Calendar shows the last valid date."));
}
