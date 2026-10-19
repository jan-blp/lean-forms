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
    for code in 0..=6 {
        let theme = Theme::from_code(code).unwrap();
        let labels: Vec<_> = (0..30).map(|i| format!("Person.Field{i}")).collect();
        let screen = Screen {
            fields: labels
                .iter()
                .map(|label| Field { label, value: "12" })
                .collect(),
            selected: 29,
            editor: Some(Editor {
                calendar: None,
                date_input: false,
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
            .draw(|frame| render(frame, &screen, &mut state, theme))
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
            .any(|cell| cell.bg == theme.selection));
    }
}

#[test]
fn choice_editor_shows_selection_and_navigation() {
    for code in 0..=6 {
        let theme = Theme::from_code(code).unwrap();
        let options = vec!["Home".into(), "Work".into(), "Other".into()];
        let screen = Screen {
            fields: vec![Field {
                label: "Address kind",
                value: "Home",
            }],
            selected: 0,
            editor: Some(Editor {
                calendar: None,
                date_input: false,
                label: "Address kind",
                text: "Home",
                error: None,
                choice: Some(1),
                options: &options,
            }),
        };
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
    }
}

#[test]
fn narrow_terminal_and_wide_text_are_handled() {
    for code in 0..=6 {
        let theme = Theme::from_code(code).unwrap();
        let screen = Screen {
            fields: vec![],
            selected: 0,
            editor: None,
        };
        let mut terminal = Terminal::new(TestBackend::new(31, 10)).unwrap();
        terminal
            .draw(|frame| render(frame, &screen, &mut TableState::default(), theme))
            .unwrap();
        assert!(contents(&terminal).contains("Enlarge terminal"));
        assert_eq!(editor_tail("Ada界", 3), "a界");
        assert_eq!(clean("Ada\n\u{1b}"), "Ada  ");
    }
}

#[test]
fn field_selection_distinguishes_labels_from_values() {
    let screen = Screen {
        fields: vec![Field {
            label: "Description",
            value: "New item",
        }],
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
        assert_eq!(highlighted.len(), " New item ".len());
        let y = highlighted[0].1;
        assert!(highlighted.iter().all(|&(_, row)| row == y));
        assert_eq!(buffer[(1, y)].symbol(), "›");
        let row: String = (0..100).map(|x| buffer[(x, y)].symbol()).collect();
        let label_x = row.chars().position(|c| c == 'D').unwrap() as u16;
        assert!(row.contains("Description:"));
        for x in label_x..label_x + "Description:".len() as u16 {
            assert_eq!(buffer[(x, y)].bg, theme.base);
            assert_eq!(buffer[(x, y)].fg, theme.subtext);
            assert!(!buffer[(x, y)].modifier.contains(Modifier::BOLD));
        }
        assert!((0..100).all(|x| buffer[(x, y - 1)].bg != theme.selection));
        assert_eq!(buffer[(90, y)].bg, theme.base);
    }
}
