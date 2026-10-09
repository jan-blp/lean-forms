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
    widgets::{Block, Borders, Cell, List, ListItem, ListState, Paragraph, Row, Table, TableState},
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

#[derive(Clone, Copy)]
struct Theme {
    base: Color,
    text: Color,
    subtext: Color,
    border: Color,
    selection: Color,
    accent: Color,
    error: Color,
}

impl Theme {
    // Catppuccin: https://catppuccin.com/palette/
    const FRAPPE: Self = Self {
        base: Color::Rgb(48, 52, 70),
        text: Color::Rgb(198, 208, 245),
        subtext: Color::Rgb(165, 173, 206),
        border: Color::Rgb(115, 121, 148),
        selection: Color::Rgb(81, 87, 109),
        accent: Color::Rgb(202, 158, 230),
        error: Color::Rgb(231, 130, 132),
    };
    const LATTE: Self = Self {
        base: Color::Rgb(239, 241, 245),
        text: Color::Rgb(76, 79, 105),
        subtext: Color::Rgb(108, 111, 133),
        border: Color::Rgb(156, 160, 176),
        selection: Color::Rgb(204, 208, 218),
        accent: Color::Rgb(136, 57, 239),
        error: Color::Rgb(210, 15, 57),
    };
    const MACCHIATO: Self = Self {
        base: Color::Rgb(36, 39, 58),
        text: Color::Rgb(202, 211, 245),
        subtext: Color::Rgb(165, 173, 203),
        border: Color::Rgb(110, 115, 141),
        selection: Color::Rgb(73, 77, 100),
        accent: Color::Rgb(198, 160, 246),
        error: Color::Rgb(237, 135, 150),
    };

    const MOCHA: Self = Self {
        base: Color::Rgb(30, 30, 46),
        text: Color::Rgb(205, 214, 244),
        subtext: Color::Rgb(166, 173, 200),
        border: Color::Rgb(108, 112, 134),
        selection: Color::Rgb(69, 71, 90),
        accent: Color::Rgb(203, 166, 247),
        error: Color::Rgb(243, 139, 168),
    };

    // Ayu: https://github.com/ayu-theme/ayu-colors/tree/master/themes

    const AYU_LIGHT: Self = Self {
        base: Color::Rgb(248, 249, 250),
        text: Color::Rgb(92, 97, 102),
        subtext: Color::Rgb(92, 97, 102),
        border: Color::Rgb(130, 142, 159),
        selection: Color::Rgb(228, 232, 235),
        accent: Color::Rgb(242, 151, 24),
        error: Color::Rgb(230, 80, 80),
    };

    const AYU_DARK: Self = Self {
        base: Color::Rgb(13, 16, 23),
        text: Color::Rgb(191, 189, 182),
        subtext: Color::Rgb(191, 189, 182),
        border: Color::Rgb(90, 99, 120),
        selection: Color::Rgb(28, 33, 43),
        accent: Color::Rgb(230, 180, 80),
        error: Color::Rgb(217, 87, 87),
    };

    // Nord: https://www.nordtheme.com/docs/colors-and-palettes/

    const NORD: Self = Self {
        base: Color::Rgb(46, 52, 64),
        text: Color::Rgb(236, 239, 244),
        subtext: Color::Rgb(216, 222, 233),
        border: Color::Rgb(76, 86, 106),
        selection: Color::Rgb(67, 76, 94),
        accent: Color::Rgb(136, 192, 208),
        error: Color::Rgb(191, 97, 106),
    };

    fn from_code(code: u8) -> Result<Self> {
        match code {
            0 => Ok(Self::FRAPPE),
            1 => Ok(Self::MACCHIATO),
            2 => Ok(Self::MOCHA),
            3 => Ok(Self::LATTE),
            4 => Ok(Self::AYU_LIGHT),
            5 => Ok(Self::AYU_DARK),
            6 => Ok(Self::NORD),
            _ => Err("Unknown theme code".into()),
        }
    }
}

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

struct Field<'a> {
    label: &'a str,
    value: &'a str,
}
struct Editor<'a> {
    label: &'a str,
    text: &'a str,
    error: Option<&'a str>,
    choice: Option<usize>,
    options: &'a [String],
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
pub extern "C" fn forms_tui_error() -> *const c_char {
    ERROR.with(|v| v.borrow().as_ptr())
}
#[no_mangle]
pub extern "C" fn forms_tui_result() -> *const c_char {
    OUTPUT.with(|v| v.borrow().as_ptr())
}
struct Session;
impl Drop for Session {
    fn drop(&mut self) {
        let _ = terminal::disable_raw_mode();
        let _ = execute!(io::stdout(), Show, LeaveAlternateScreen);
    }
}
fn run(engine: &mut Engine, theme: Theme, interrupted: extern "C" fn() -> i32) -> Result<()> {
    if !io::stdin().is_terminal() || !io::stdout().is_terminal() {
        return Err("The TUI needs an interactive terminal.".into());
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
                        choice: e.choice,
                        options: &e.options,
                    })
                }),
            };
            terminal.draw(|frame| render(frame, &screen, &mut table, theme))?;
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
pub unsafe extern "C" fn forms_tui_run(
    data: *const u8,
    len: usize,
    theme: u8,
    interrupted: extern "C" fn() -> i32,
) -> i32 {
    let outcome = catch_unwind(AssertUnwindSafe(|| -> Result<()> {
        if data.is_null() {
            return Err("Null specification".into());
        }
        let json = std::str::from_utf8(unsafe { std::slice::from_raw_parts(data, len) })?;
        let mut engine = Engine::parse(json)?;
        run(&mut engine, Theme::from_code(theme)?, interrupted)?;
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

fn render(frame: &mut Frame, screen: &Screen, table_state: &mut TableState, theme: Theme) {
    let area = frame.area();
    frame.render_widget(
        Block::default().style(Style::default().fg(theme.text).bg(theme.base)),
        area,
    );
    if area.width < 32 || area.height < 12 {
        frame.render_widget(Paragraph::new("Enlarge terminal to at least 32 x 12"), area);
        return;
    }
    let footer_height = match &screen.editor {
        Some(editor) if editor.choice.is_some() => (editor
            .options
            .len()
            .saturating_add(4)
            .min(u16::MAX as usize) as u16)
            .min(area.height.saturating_sub(7)),
        Some(_) => 6,
        None => 3,
    };
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
                .border_style(Style::default().fg(theme.accent)),
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
            .style(Style::default().fg(theme.accent))
            .bottom_margin(1),
    )
    .block(
        Block::bordered()
            .border_style(Style::default().fg(theme.border))
            .title(" Form ")
            .title_bottom(
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
            .bg(theme.selection)
            .fg(theme.text)
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
        if let Some(index) = editor.choice {
            let parts =
                Layout::vertical([Constraint::Min(3), Constraint::Length(2)]).split(sections[2]);
            let options = List::new(
                editor
                    .options
                    .iter()
                    .map(|label| ListItem::new(clean(label))),
            )
            .block(
                Block::bordered()
                    .title(format!(" {} ", clean(editor.label)))
                    .title_bottom(
                        Line::from(format!(" {} / {} ", index + 1, editor.options.len()))
                            .right_aligned(),
                    )
                    .border_style(Style::default().fg(theme.accent)),
            )
            .highlight_style(
                Style::default()
                    .bg(theme.selection)
                    .fg(theme.text)
                    .add_modifier(Modifier::BOLD),
            )
            .highlight_symbol("› ");
            let mut state = ListState::default().with_selected(Some(index));
            frame.render_stateful_widget(options, parts[0], &mut state);
            frame.render_widget(
                Paragraph::new("↑/↓ or j/k choose · Enter save · Esc cancel")
                    .style(Style::default().fg(theme.subtext)),
                parts[1],
            );
            return;
        }
        let parts = Layout::vertical([
            Constraint::Length(3),
            Constraint::Length(1),
            Constraint::Length(2),
        ])
        .split(sections[2]);
        let text = format!(
            "{}▏",
            editor_tail(&clean(&editor.text), parts[0].width.saturating_sub(3))
        );
        let border = if editor.error.is_some() {
            theme.error
        } else {
            theme.accent
        };
        frame.render_widget(
            Paragraph::new(text).block(
                Block::bordered()
                    .title(format!(" {} ", clean(&editor.label)))
                    .border_style(Style::default().fg(border)),
            ),
            parts[0],
        );
        if let Some(error) = &editor.error {
            frame.render_widget(
                Paragraph::new(clean(error)).style(Style::default().fg(theme.error)),
                parts[1],
            );
        }
        frame.render_widget(
            Paragraph::new("Enter save · Esc cancel · Backspace delete · Ctrl-U clear")
                .style(Style::default().fg(theme.subtext)),
            parts[2],
        );
    } else {
        frame.render_widget(
            Paragraph::new("j/k or ↑/↓ select · i/Enter edit · Space toggle · q quit")
                .style(Style::default().fg(theme.subtext))
                .block(
                    Block::default()
                        .borders(Borders::TOP)
                        .border_style(Style::default().fg(theme.border)),
                ),
            sections[2],
        );
    }
}

#[cfg(test)]
mod tests;
