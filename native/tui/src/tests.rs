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
                label,
                value: "12",
                section: "",
                action: false,
            })
            .collect(),
        selected: 29,
        editor: Some(Editor {
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
            label: "Address kind",
            value: "Home",
            section: "",
            action: false,
        }],
        selected: 0,
        editor: Some(Editor {
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
    engine.selected = 4;
    engine.step(Key::Enter);
    let fields = engine.fields();
    let values: Vec<_> = fields.iter().map(|field| engine.shown(field)).collect();
    let mut screen = Screen {
        fields: fields
            .iter()
            .zip(&values)
            .map(|(field, value)| Field {
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
