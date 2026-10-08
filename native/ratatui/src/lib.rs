use crossterm::{
    cursor::{Hide, Show},
    event::{self, Event, KeyCode, KeyEventKind, KeyModifiers},
    execute,
    terminal::{self, EnterAlternateScreen, LeaveAlternateScreen},
};
use ratatui::{
    backend::CrosstermBackend,
    layout::{Constraint, Layout},
    style::{Color, Modifier, Style},
    text::Line,
    widgets::{Block, Borders, Cell, Paragraph, Row, Table, TableState},
    Frame, Terminal,
};
use std::{
    cell::RefCell,
    ffi::{c_char, CString},
    io::{self, IsTerminal},
    panic::{catch_unwind, AssertUnwindSafe},
    time::Duration,
};
use unicode_width::UnicodeWidthChar;

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

struct Field<'a> {
    label: &'a str,
    value: &'a str,
}
struct Editor<'a> {
    label: &'a str,
    text: &'a str,
    error: Option<&'a str>,
}
struct Screen<'a> {
    fields: Vec<Field<'a>>,
    selected: usize,
    editor: Option<Editor<'a>>,
}
mod interpreter;
use interpreter::{Engine, Key};
thread_local! {
    static ERROR: RefCell<CString> = RefCell::new(CString::new("").unwrap());
    static OUTPUT: RefCell<CString> = RefCell::new(CString::new("").unwrap());
}
#[no_mangle]
pub extern "C" fn forms_ratatui_error() -> *const c_char {
    ERROR.with(|v| v.borrow().as_ptr())
}
#[no_mangle]
pub extern "C" fn forms_ratatui_result() -> *const c_char {
    OUTPUT.with(|v| v.borrow().as_ptr())
}
struct Session;
impl Drop for Session {
    fn drop(&mut self) {
        let _ = terminal::disable_raw_mode();
        let _ = execute!(io::stdout(), Show, LeaveAlternateScreen);
    }
}
fn run(engine: &mut Engine, interrupted: extern "C" fn() -> i32) -> Result<()> {
    if !io::stdin().is_terminal() || !io::stdout().is_terminal() {
        return Err("The TUI needs an interactive terminal. Use --plain for line input.".into());
    }
    terminal::enable_raw_mode()?;
    let _session = Session;
    execute!(io::stdout(), EnterAlternateScreen, Hide)?;
    let mut terminal = Terminal::new(CrosstermBackend::new(io::stdout()))?;
    terminal.clear()?;
    let mut table = TableState::default();
    let mut dirty = true;
    loop {
        if dirty {
            let fields = engine.fields();
            let values: Vec<_> = fields.iter().map(|f| engine.shown(f)).collect();
            let screen = Screen {
                fields: fields
                    .iter()
                    .zip(&values)
                    .map(|(f, value)| Field {
                        label: &f.label,
                        value,
                    })
                    .collect(),
                selected: engine.selected,
                editor: engine.editor.as_ref().and_then(|e| {
                    fields.get(engine.selected).map(|f| Editor {
                        label: &f.label,
                        text: &e.text,
                        error: e.error.as_deref(),
                    })
                }),
            };
            terminal.draw(|frame| render(frame, &screen, &mut table))?;
            dirty = false;
        }
        if interrupted() != 0 {
            break;
        }
        if !event::poll(Duration::from_millis(100))? {
            continue;
        }
        let key = match event::read()? {
            Event::Resize(_, _) => {
                dirty = true;
                continue;
            }
            Event::Key(key) if key.kind != KeyEventKind::Release => key,
            _ => continue,
        };
        let key = match key.code {
            KeyCode::Up => Key::Up,
            KeyCode::Down => Key::Down,
            KeyCode::Enter => Key::Enter,
            KeyCode::Esc => Key::Escape,
            KeyCode::Backspace => Key::Backspace,
            KeyCode::Char('u') if key.modifiers.contains(KeyModifiers::CONTROL) => Key::Clear,
            KeyCode::Char('c' | 'd' | 'z') if key.modifiers.contains(KeyModifiers::CONTROL) => {
                Key::Quit
            }
            KeyCode::Char(c)
                if !key
                    .modifiers
                    .intersects(KeyModifiers::CONTROL | KeyModifiers::ALT) =>
            {
                Key::Character(c)
            }
            _ => continue,
        };
        if !engine.step(key) {
            break;
        }
        dirty = true;
    }
    Ok(())
}
/// # Safety
/// `data` must reference `len` readable bytes for this call; `interrupted` must
/// remain callable throughout the session. Input is copied; no pointers are retained.
#[no_mangle]
pub unsafe extern "C" fn forms_ratatui_run(
    data: *const u8,
    len: usize,
    interrupted: extern "C" fn() -> i32,
) -> i32 {
    let outcome = catch_unwind(AssertUnwindSafe(|| -> Result<()> {
        if data.is_null() {
            return Err("Null specification".into());
        }
        let json = std::str::from_utf8(unsafe { std::slice::from_raw_parts(data, len) })?;
        let mut engine = Engine::parse(json)?;
        run(&mut engine, interrupted)?;
        OUTPUT.with(|v| *v.borrow_mut() = CString::new(engine.result()).unwrap());
        Ok(())
    }));
    let message = match outcome {
        Ok(Ok(())) => return 0,
        Ok(Err(e)) => e.to_string(),
        Err(_) => "Form interpreter panicked".into(),
    };
    ERROR.with(|v| *v.borrow_mut() = CString::new(message.replace('\0', " ")).unwrap());
    -1
}

fn clean(text: &str) -> String {
    text.chars()
        .map(|c| if c.is_control() { ' ' } else { c })
        .collect()
}

fn editor_tail(text: &str, width: u16) -> String {
    let mut used = 0;
    let mut chars = Vec::new();
    for c in text.chars().rev() {
        used += c.width().unwrap_or(0);
        if used > width as usize {
            break;
        }
        chars.push(c);
    }
    chars.into_iter().rev().collect()
}

fn render(frame: &mut Frame, screen: &Screen, table_state: &mut TableState) {
    let area = frame.area();
    if area.width < 32 || area.height < 12 {
        frame.render_widget(Paragraph::new("Enlarge terminal to at least 32 x 12"), area);
        return;
    }
    let footer_height = if screen.editor.is_some() { 6 } else { 3 };
    let sections = Layout::vertical([
        Constraint::Length(3),
        Constraint::Min(4),
        Constraint::Length(footer_height),
    ])
    .split(area);
    frame.render_widget(
        Paragraph::new("Typed forms · live validation").block(
            Block::bordered()
                .title(" Lean Forms ")
                .border_style(Style::default().fg(Color::Cyan)),
        ),
        sections[0],
    );
    let rows = screen.fields.iter().map(|field| {
        Row::new([
            Cell::from(clean(&field.label)),
            Cell::from(clean(&field.value)),
        ])
    });
    let table = Table::new(
        rows,
        [Constraint::Percentage(65), Constraint::Percentage(35)],
    )
    .header(
        Row::new(["Field", "Value"])
            .style(Style::default().fg(Color::Cyan))
            .bottom_margin(1),
    )
    .block(
        Block::bordered().title(" Form ").title_bottom(
            Line::from(format!(
                " {} / {} ",
                if screen.fields.is_empty() {
                    0
                } else {
                    screen.selected + 1
                },
                screen.fields.len()
            ))
            .right_aligned(),
        ),
    )
    .row_highlight_style(
        Style::default()
            .bg(Color::Blue)
            .fg(Color::White)
            .add_modifier(Modifier::BOLD),
    )
    .highlight_symbol("› ");
    table_state.select(if screen.fields.is_empty() {
        None
    } else {
        Some(screen.selected)
    });
    frame.render_stateful_widget(table, sections[1], table_state);
    if let Some(editor) = &screen.editor {
        let parts = Layout::vertical([
            Constraint::Length(3),
            Constraint::Length(1),
            Constraint::Length(2),
        ])
        .split(sections[2]);
        let text = editor_tail(&clean(&editor.text), parts[0].width.saturating_sub(3));
        let border = if editor.error.is_some() {
            Color::Red
        } else {
            Color::Cyan
        };
        frame.render_widget(
            Paragraph::new(format!("{text}▏")).block(
                Block::bordered()
                    .title(format!(" {} ", clean(&editor.label)))
                    .border_style(Style::default().fg(border)),
            ),
            parts[0],
        );
        if let Some(error) = &editor.error {
            frame.render_widget(
                Paragraph::new(clean(error)).style(Style::default().fg(Color::Red)),
                parts[1],
            );
        }
        frame.render_widget(
            Paragraph::new("Enter save · Esc cancel · Backspace delete · Ctrl-U clear"),
            parts[2],
        );
    } else {
        frame.render_widget(
            Paragraph::new("j/k or ↑/↓ select · i/Enter edit · Space toggle · q quit")
                .block(Block::default().borders(Borders::TOP)),
            sections[2],
        );
    }
}

#[cfg(test)]
mod tests {
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
            fields: labels
                .iter()
                .map(|label| Field { label, value: "12" })
                .collect(),
            selected: 29,
            editor: Some(Editor {
                label: "Person.Field29".into(),
                text: "-1".into(),
                error: Some("Enter a non-negative whole number.".into()),
            }),
        };
        let mut terminal = Terminal::new(TestBackend::new(80, 24)).unwrap();
        let mut state = TableState::default();
        terminal
            .draw(|frame| render(frame, &screen, &mut state))
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
            .any(|cell| cell.bg == Color::Blue));
    }

    #[test]
    fn narrow_terminal_and_wide_text_are_handled() {
        let screen = Screen {
            fields: vec![],
            selected: 0,
            editor: None,
        };
        let mut terminal = Terminal::new(TestBackend::new(31, 10)).unwrap();
        terminal
            .draw(|frame| render(frame, &screen, &mut TableState::default()))
            .unwrap();
        assert!(contents(&terminal).contains("Enlarge terminal"));
        assert_eq!(editor_tail("Ada界", 3), "a界");
        assert_eq!(clean("Ada\n\u{1b}"), "Ada  ");
    }
}
