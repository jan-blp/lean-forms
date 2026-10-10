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
            .map(|label| Field { label, value: "12" })
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
