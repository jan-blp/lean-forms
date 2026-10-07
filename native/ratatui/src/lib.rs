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
struct App {
    terminal: Terminal<CrosstermBackend<io::Stdout>>,
    table: TableState,
}

thread_local! {
    static APP: RefCell<Option<App>> = const { RefCell::new(None) };
    static ERROR: RefCell<CString> = RefCell::new(CString::new("").unwrap());
}

fn boundary(action: impl FnOnce() -> Result<i32>) -> i32 {
    let outcome = catch_unwind(AssertUnwindSafe(action));
    let message = match outcome {
        Ok(Ok(value)) => return value,
        Ok(Err(error)) => error.to_string(),
        Err(_) => "Ratatui adapter panicked".to_owned(),
    };
    ERROR.with(|error| *error.borrow_mut() = CString::new(message.replace('\0', " ")).unwrap());
    -1
}

fn restore() {
    let _ = terminal::disable_raw_mode();
    let _ = execute!(io::stdout(), Show, LeaveAlternateScreen);
}

#[no_mangle]
pub extern "C" fn forms_ratatui_error() -> *const c_char {
    ERROR.with(|error| error.borrow().as_ptr())
}

#[no_mangle]
pub extern "C" fn forms_ratatui_start() -> i32 {
    boundary(|| {
        if !io::stdin().is_terminal() || !io::stdout().is_terminal() {
            return Ok(0);
        }
        terminal::enable_raw_mode()?;
        let setup = (|| -> Result<App> {
            execute!(io::stdout(), EnterAlternateScreen, Hide)?;
            let mut terminal = Terminal::new(CrosstermBackend::new(io::stdout()))?;
            terminal.clear()?;
            Ok(App {
                terminal,
                table: TableState::default(),
            })
        })();
        match setup {
            Ok(app) => APP.with(|state| *state.borrow_mut() = Some(app)),
            Err(error) => {
                restore();
                return Err(error);
            }
        }
        Ok(1)
    })
}

#[no_mangle]
pub extern "C" fn forms_ratatui_stop() -> i32 {
    boundary(|| {
        APP.with(|app| {
            app.borrow_mut().take();
        });
        restore();
        Ok(0)
    })
}

#[no_mangle]
pub extern "C" fn forms_ratatui_key() -> i32 {
    boundary(|| {
        if !event::poll(Duration::from_millis(100))? {
            return Ok(0);
        }
        let Event::Key(key) = event::read()? else {
            return Ok(0);
        };
        if key.kind == KeyEventKind::Release {
            return Ok(0);
        }
        Ok(match key.code {
            KeyCode::Up => 1,
            KeyCode::Down => 2,
            KeyCode::Enter => 3,
            KeyCode::Esc => 4,
            KeyCode::Backspace => 5,
            KeyCode::Char('u') if key.modifiers.contains(KeyModifiers::CONTROL) => 6,
            KeyCode::Char('c' | 'd' | 'z') if key.modifiers.contains(KeyModifiers::CONTROL) => 7,
            KeyCode::Char(char)
                if !key
                    .modifiers
                    .intersects(KeyModifiers::CONTROL | KeyModifiers::ALT) =>
            {
                char as i32 + 256
            }
            _ => 0,
        })
    })
}

#[no_mangle]
pub extern "C" fn forms_ratatui_size() -> i32 {
    boundary(|| {
        let (columns, rows) = terminal::size()?;
        Ok(((rows as i32) << 16) | columns as i32)
    })
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

// These layouts mirror native/screen.h. The C shim owns the temporary array
// and borrows Lean strings; Rust never stores their pointers after draw returns.
#[repr(C)]
pub struct FormsString {
    data: *const u8,
    len: usize,
}
#[repr(C)]
pub struct FormsField {
    label: FormsString,
    value: FormsString,
}
#[repr(C)]
pub struct FormsEditor {
    label: FormsString,
    text: FormsString,
    error: *const FormsString,
}
#[repr(C)]
pub struct FormsScreen {
    fields: *const FormsField,
    field_count: usize,
    selected: usize,
    editor: *const FormsEditor,
}

impl FormsString {
    // The caller guarantees that the byte span lives as long as this borrow.
    unsafe fn view(&self) -> Result<&str> {
        if self.len == 0 {
            return Ok("");
        }
        if self.data.is_null() {
            return Err("Null string data".into());
        }
        Ok(std::str::from_utf8(unsafe {
            std::slice::from_raw_parts(self.data, self.len)
        })?)
    }
}

impl FormsScreen {
    unsafe fn view(&self) -> Result<Screen<'_>> {
        let fields = if self.field_count == 0 {
            &[][..]
        } else {
            if self.fields.is_null() {
                return Err("Null field array".into());
            }
            unsafe { std::slice::from_raw_parts(self.fields, self.field_count) }
        };
        let fields = fields
            .iter()
            .map(|field| -> Result<Field<'_>> {
                Ok(Field {
                    label: unsafe { field.label.view() }?,
                    value: unsafe { field.value.view() }?,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        if !fields.is_empty() && self.selected >= fields.len() {
            return Err("Selected field is out of bounds".into());
        }
        let editor = unsafe { self.editor.as_ref() }
            .map(|editor| -> Result<Editor<'_>> {
                Ok(Editor {
                    label: unsafe { editor.label.view() }?,
                    text: unsafe { editor.text.view() }?,
                    error: unsafe { editor.error.as_ref() }
                        .map(|error| unsafe { error.view() })
                        .transpose()?,
                })
            })
            .transpose()?;
        Ok(Screen {
            fields,
            selected: self.selected,
            editor,
        })
    }
}

/// # Safety
/// `screen` and all nested pointers must match screen.h and remain valid,
/// aligned, and immutable until this function returns. No pointers are retained.
#[no_mangle]
pub unsafe extern "C" fn forms_ratatui_draw(screen: *const FormsScreen) -> i32 {
    boundary(|| {
        let screen = unsafe { screen.as_ref() }.ok_or("Null screen")?;
        let screen = unsafe { screen.view() }?;
        APP.with(|state| -> Result<i32> {
            let mut state = state.borrow_mut();
            let app = state.as_mut().ok_or("Terminal is not initialized")?;
            app.terminal
                .draw(|frame| render(frame, &screen, &mut app.table))?;
            Ok(0)
        })
    })
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

    fn span(text: &str) -> FormsString {
        FormsString {
            data: text.as_ptr(),
            len: text.len(),
        }
    }

    #[test]
    fn ffi_borrows_utf8_spans_and_preserves_optional_empty_strings() {
        let text = "Zoé\0界";
        let fields = [FormsField {
            label: span("Person.Name"),
            value: span(text),
        }];
        let error = span("");
        let editor = FormsEditor {
            label: span("Person.Name"),
            text: span(text),
            error: &error,
        };
        let raw = FormsScreen {
            fields: fields.as_ptr(),
            field_count: 1,
            selected: 0,
            editor: &editor,
        };
        let screen = unsafe { raw.view() }.unwrap();
        assert_eq!(screen.fields[0].value, text);
        assert_eq!(screen.fields[0].value.as_ptr(), text.as_ptr());
        assert_eq!(screen.editor.as_ref().unwrap().error, Some(""));
        assert_eq!(screen.editor.as_ref().unwrap().text, text);
        let empty = FormsScreen {
            fields: std::ptr::null(),
            field_count: 0,
            selected: 0,
            editor: std::ptr::null(),
        };
        let screen = unsafe { empty.view() }.unwrap();
        assert!(screen.fields.is_empty());
        assert!(screen.editor.is_none());
    }

    #[test]
    fn ffi_rejects_invalid_utf8_and_selection() {
        let invalid = [255u8];
        let text = FormsString {
            data: invalid.as_ptr(),
            len: invalid.len(),
        };
        assert!(unsafe { text.view() }.is_err());
        let fields = [FormsField {
            label: span("Name"),
            value: span("Ada"),
        }];
        let raw = FormsScreen {
            fields: fields.as_ptr(),
            field_count: 1,
            selected: 1,
            editor: std::ptr::null(),
        };
        assert!(unsafe { raw.view() }.is_err());
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
