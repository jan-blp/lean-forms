use chrono::{Datelike, NaiveDate};
use crossterm::{
    cursor::{Hide, Show},
    event::{self, Event, KeyCode, KeyEventKind, KeyModifiers},
    execute,
    terminal::{self, EnterAlternateScreen, LeaveAlternateScreen},
};
use ratatui::{
    backend::CrosstermBackend,
    layout::{Constraint, Layout, Rect},
    style::{Color, Modifier, Style},
    text::{Line, Span},
    widgets::{
        Block, Borders, Cell, Clear, List, ListItem, ListState, Paragraph, Row, Table, TableState,
    },
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
    computed: Color,
    add: Color,
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
        computed: Color::Rgb(129, 200, 190),
        add: Color::Rgb(166, 209, 137),
        error: Color::Rgb(231, 130, 132),
    };
    const LATTE: Self = Self {
        base: Color::Rgb(239, 241, 245),
        text: Color::Rgb(76, 79, 105),
        subtext: Color::Rgb(108, 111, 133),
        border: Color::Rgb(156, 160, 176),
        selection: Color::Rgb(204, 208, 218),
        accent: Color::Rgb(136, 57, 239),
        computed: Color::Rgb(23, 146, 153),
        add: Color::Rgb(64, 160, 43),
        error: Color::Rgb(210, 15, 57),
    };
    const MACCHIATO: Self = Self {
        base: Color::Rgb(36, 39, 58),
        text: Color::Rgb(202, 211, 245),
        subtext: Color::Rgb(165, 173, 203),
        border: Color::Rgb(110, 115, 141),
        selection: Color::Rgb(73, 77, 100),
        accent: Color::Rgb(198, 160, 246),
        computed: Color::Rgb(139, 213, 202),
        add: Color::Rgb(166, 218, 149),
        error: Color::Rgb(237, 135, 150),
    };

    const MOCHA: Self = Self {
        base: Color::Rgb(30, 30, 46),
        text: Color::Rgb(205, 214, 244),
        subtext: Color::Rgb(166, 173, 200),
        border: Color::Rgb(108, 112, 134),
        selection: Color::Rgb(69, 71, 90),
        accent: Color::Rgb(203, 166, 247),
        computed: Color::Rgb(148, 226, 213),
        add: Color::Rgb(166, 227, 161),
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
        computed: Color::Rgb(38, 143, 139),
        add: Color::Rgb(88, 140, 26),
        error: Color::Rgb(230, 80, 80),
    };

    const AYU_DARK: Self = Self {
        base: Color::Rgb(13, 16, 23),
        text: Color::Rgb(191, 189, 182),
        subtext: Color::Rgb(191, 189, 182),
        border: Color::Rgb(90, 99, 120),
        selection: Color::Rgb(28, 33, 43),
        accent: Color::Rgb(230, 180, 80),
        computed: Color::Rgb(95, 214, 189),
        add: Color::Rgb(170, 217, 76),
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
        computed: Color::Rgb(163, 190, 140),
        add: Color::Rgb(163, 190, 140),
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
    presentation: interpreter::Presentation,
    label: &'a str,
    value: &'a str,
    section: &'a str,
    action: bool,
}
struct Editor<'a> {
    calendar: Option<NaiveDate>,
    date_input: bool,
    constructor: bool,
    label: &'a str,
    text: &'a str,
    error: Option<&'a str>,
    choice: Option<usize>,
    options: &'a [String],
}
struct Screen<'a> {
    tables: &'a [interpreter::ReportTable],
    table_offset: usize,
    fields: Vec<Field<'a>>,
    errors: Vec<String>,
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
            let (fields, report_tables) = engine.content();
            let values: Vec<_> = fields.iter().map(|f| engine.shown(f)).collect();
            let screen = Screen {
                tables: &report_tables,
                table_offset: engine.table_offset,
                errors: engine.errors(),
                fields: fields
                    .iter()
                    .zip(&values)
                    .map(|(f, value)| Field {
                        presentation: f.presentation,
                        label: &f.title,
                        section: &f.section,
                        action: f.action,
                        value,
                    })
                    .collect(),
                selected: engine.selected,
                editor: engine.editor.as_ref().and_then(|e| {
                    fields.get(engine.selected).map(|f| Editor {
                        calendar: e.calendar,
                        date_input: e.date_input,
                        constructor: f.presentation.constructor,
                        label: &f.title,
                        text: &e.text,
                        error: e.error.as_deref(),
                        choice: e.choice,
                        options: &e.options,
                    })
                }),
            };
            let mut viewports = Vec::new();
            terminal.draw(|frame| {
                viewports = render_with_viewports(frame, &screen, &mut table, theme);
            })?;
            engine.set_table_viewports(viewports);
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
            KeyCode::Left => Key::Left,
            KeyCode::Right => Key::Right,
            KeyCode::PageUp => Key::PageUp,
            KeyCode::PageDown => Key::PageDown,
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

fn render_report_tables(
    frame: &mut Frame,
    tables: &[interpreter::ReportTable],
    offset: usize,
    area: ratatui::layout::Rect,
    theme: Theme,
) -> Vec<usize> {
    let areas = Layout::vertical(tables.iter().map(|_| Constraint::Min(3))).split(area);
    for (table, area) in tables.iter().zip(areas.iter()) {
        let block = Block::bordered()
            .border_style(Style::default().fg(theme.border))
            .title(format!(" Results · {} rows ", table.rows.len()));
        if table.rows.is_empty() {
            frame.render_widget(Paragraph::new("No matching results").block(block), *area);
            continue;
        }
        let rows = table
            .rows
            .iter()
            .map(|row| Row::new(row.iter().map(|cell| clean(cell))));
        let widths = table
            .columns
            .iter()
            .map(|_| Constraint::Ratio(1, table.columns.len() as u32));
        let widget = Table::new(rows, widths)
            .header(
                Row::new(table.columns.iter().map(|label| clean(label))).style(
                    Style::default()
                        .fg(theme.accent)
                        .add_modifier(Modifier::BOLD),
                ),
            )
            .column_spacing(2)
            .block(block);
        let visible_rows = usize::from(area.height.saturating_sub(3)).max(1);
        let mut state = TableState::default()
            .with_offset(offset.min(table.rows.len().saturating_sub(visible_rows)));
        frame.render_stateful_widget(widget, *area, &mut state);
    }
    areas.iter().map(|area| usize::from(area.height.saturating_sub(3)).max(1)).collect()
}

#[cfg(test)]
fn render(frame: &mut Frame, screen: &Screen, table_state: &mut TableState, theme: Theme) {
    render_with_viewports(frame, screen, table_state, theme);
}

fn render_with_viewports(frame: &mut Frame, screen: &Screen, table_state: &mut TableState, theme: Theme) -> Vec<usize> {
    let fields: Vec<_> = screen.fields.iter().filter(|field| !field.presentation.text).collect();
    let selected = screen.fields.iter().take(screen.selected)
        .filter(|field| !field.presentation.text).count();
    let summaries: Vec<_> = screen.fields.iter().filter(|field| field.presentation.text)
        .map(|field| Line::styled(clean(field.value), Style::default().fg(theme.computed)))
        .collect();
    let area = frame.area();
    frame.render_widget(
        Block::default().style(Style::default().fg(theme.text).bg(theme.base)),
        area,
    );
    if area.width < 32 || area.height < 12 {
        frame.render_widget(Paragraph::new("Enlarge terminal to at least 32 x 12"), area);
        return vec![];
    }
    let footer_height = match &screen.editor {
        Some(editor) if editor.calendar.is_some() => 3,
        Some(editor) if editor.choice.is_some() => (editor
            .options
            .len()
            .saturating_add(4)
            .min(u16::MAX as usize) as u16)
            .min(area.height.saturating_sub(7)),
        Some(_) => 6,
        None => 3,
    };
    let error_height = if screen.errors.is_empty() {
        0
    } else {
        (screen.errors.len() as u16 + 2).min(area.height.saturating_sub(footer_height + 7))
    };
    let sections = Layout::vertical([
        Constraint::Length(if screen.tables.is_empty() { 3 } else { 2 }),
        Constraint::Min(4),
        Constraint::Length(error_height),
        Constraint::Length(footer_height),
    ])
    .split(area);
    let compact_summary = area.height < 14 && !summaries.is_empty();
    let summary_height = if compact_summary { 0 } else {
        (summaries.len() as u16).min(sections[1].height.saturating_sub(4))
    };
    let body_areas = Layout::vertical([Constraint::Length(summary_height), Constraint::Min(4)])
        .split(sections[1]);
    frame.render_widget(Paragraph::new(summaries.clone()), body_areas[0]);
    let content_area = body_areas[1];
    let content_areas = if screen.tables.is_empty() {
        vec![content_area]
    } else if area.width >= 100 {
        Layout::horizontal([Constraint::Percentage(45), Constraint::Percentage(55)])
            .split(content_area).to_vec()
    } else {
        let controls_height =
            (fields.len() as u16 + 5).min(content_area.height.saturating_sub(4));
        Layout::vertical([Constraint::Length(controls_height), Constraint::Min(4)])
            .split(content_area)
            .to_vec()
    };
    let title = fields
        .first()
        .map(|field| field.section.split(" › ").next().unwrap_or("Form"))
        .filter(|title| !title.is_empty())
        .unwrap_or("Form");
    let title = if screen.tables.is_empty() {
        title
    } else {
        "Report"
    };
    let status = if screen.errors.is_empty() {
        if screen.tables.is_empty() {
            "Ready to submit".to_owned()
        } else {
            "PgUp/PgDn scroll results".to_owned()
        }
    } else {
        format!(
            "{} validation issue{}",
            screen.errors.len(),
            if screen.errors.len() == 1 { "" } else { "s" }
        )
    };
    frame.render_widget(
        Paragraph::new(Line::from(vec![
            ratatui::text::Span::styled(
                format!("  {}", clean(title)),
                Style::default()
                    .fg(theme.accent)
                    .add_modifier(Modifier::BOLD),
            ),
            ratatui::text::Span::styled(
                format!("   {status}"),
                Style::default().fg(if screen.errors.is_empty() {
                    theme.subtext
                } else {
                    theme.error
                }),
            ),
        ]))
        .block(
            Block::default()
                .borders(Borders::BOTTOM)
                .border_style(Style::default().fg(theme.border)),
        ),
        sections[0],
    );
    if compact_summary {
        frame.render_widget(Paragraph::new(summaries).block(
            Block::default().borders(Borders::BOTTOM)
                .border_style(Style::default().fg(theme.border))), sections[0]);
    }
    let label_width = fields
        .iter()
        .map(|field| {
            field
                .label
                .chars()
                .map(|c| c.width().unwrap_or(0))
                .sum::<usize>()
                .max(
                    field
                        .section
                        .chars()
                        .map(|c| c.width().unwrap_or(0))
                        .sum::<usize>(),
                )
                + 5
                + if field.action { 4 } else { 0 }
                + field.presentation.depth.min(4) * 2
        })
        .max()
        .unwrap_or(20)
        .min(38) as u16;
    let rows = fields.iter().enumerate().map(|(index, field)| {
        let heading = (screen.tables.is_empty() || area.height >= 18)
            && !field.section.is_empty()
            && !(index == 0 && field.presentation.constructor && field.section == title)
            && (index == 0 || fields[index - 1].section != field.section);
        let selected = index == selected;
        let selection = Style::default()
            .bg(theme.selection)
            .fg(theme.text)
            .add_modifier(Modifier::BOLD);
        let label_style = if field.presentation.disabled {
            (if selected && !field.action {
                selection
            } else {
                Style::default()
            })
            .fg(theme.subtext)
        } else if field.presentation.computed {
            (if selected {
                selection
            } else {
                Style::default()
            })
            .fg(theme.computed)
        } else if field.action {
            let color = if field.presentation.button {
                theme.accent
            } else if field.presentation.add {
                theme.add
            } else {
                theme.error
            };
            let style = Style::default().fg(color);
            if selected { style.add_modifier(Modifier::BOLD) } else { style }
        } else if selected {
            selection
        } else {
            Style::default().fg(if field.action {
                theme.accent
            } else {
                theme.text
            })
        };
        let mut label_spans = vec![
            ratatui::text::Span::styled(
                if selected { "› " } else { "  " },
                Style::default().fg(theme.accent),
            ),
            ratatui::text::Span::styled(
                "│ ".repeat(field.presentation.depth.min(4)),
                Style::default().fg(theme.border),
            ),
        ];
        label_spans.push(ratatui::text::Span::styled(
            if field.action {
                format!(" [ {} ] ", clean(field.label))
            } else {
                format!(" {} ", clean(field.label))
            },
            label_style,
        ));
        let label = Line::from(label_spans);
        let value = if field.presentation.text {
            clean(field.value)
        } else if field.presentation.computed {
            format!("{} [computed]", clean(field.value))
        } else if field.presentation.disabled {
            format!(
                "{} [disabled]",
                if field.action {
                    String::new()
                } else {
                    clean(field.value)
                }
            )
        } else if field.presentation.constructor || field.presentation.choice {
            format!(
                "{} ▾{}",
                clean(field.value),
                if field.presentation.invalid { " !" } else { "" }
            )
        } else if field.action {
            if selected { "Enter ↵".into() } else { String::new() }
        } else if field.value.is_empty() {
            "—".into()
        } else {
            clean(field.value)
        };
        let value_style = if field.presentation.invalid {
            (if selected && !field.action {
                selection
            } else {
                Style::default()
            })
            .fg(theme.error)
        } else if field.presentation.disabled {
            (if selected && !field.action {
                selection
            } else {
                Style::default()
            })
            .fg(theme.subtext)
        } else if field.presentation.computed {
            (if selected && !field.action {
                selection
            } else {
                Style::default()
            })
            .fg(theme.computed)
        } else if field.action {
            (if selected && !field.action {
                selection
            } else {
                Style::default()
            })
            .fg(if field.presentation.button {
                theme.accent
            } else if field.presentation.add {
                theme.add
            } else {
                theme.error
            })
            .add_modifier(Modifier::BOLD)
        } else if selected && !field.action {
            selection
        } else if field.presentation.constructor || field.presentation.choice {
            Style::default()
                .fg(theme.accent)
                .add_modifier(Modifier::BOLD)
        } else {
            Style::default().fg(if field.action || field.value.is_empty() {
                theme.subtext
            } else {
                theme.text
            })
        };
        let value = Line::from(ratatui::text::Span::styled(
            format!(" {value} "),
            value_style,
        ));
        let mut labels = Vec::new();
        let mut values = Vec::new();
        if heading {
            labels.push(Line::styled(
                clean(field.section),
                Style::default().fg(theme.accent),
            ));
            values.push(Line::default());
        }
        labels.push(label);
        values.push(value);
        if let Some(note) = field.presentation.note {
            let available = sections[1]
                .width
                .saturating_sub(label_width.min(content_areas[0].width.saturating_sub(14).max(8)) + 6)
                as usize;
            let mut line = String::new();
            for word in note.split_whitespace() {
                if !line.is_empty() && line.len() + 1 + word.len() > available {
                    labels.push(Line::default());
                    values.push(Line::styled(
                        format!(" {line}"),
                        Style::default().fg(theme.subtext),
                    ));
                    line.clear();
                }
                if !line.is_empty() {
                    line.push(' ');
                }
                line.push_str(word);
            }
            labels.push(Line::default());
            values.push(Line::styled(
                format!(" {line}"),
                Style::default().fg(theme.subtext),
            ));
        }
        let height = labels.len() as u16;
        Row::new([
            Cell::from(ratatui::text::Text::from(labels)),
            Cell::from(ratatui::text::Text::from(values)),
        ])
        .height(height)
        .top_margin(u16::from(heading))
    });
    let table = Table::new(
        rows,
        [
            Constraint::Length(label_width.min(content_areas[0].width.saturating_sub(14).max(8))),
            Constraint::Min(10),
        ],
    )
    .column_spacing(2)
    .block(
        Block::bordered()
            .border_style(Style::default().fg(theme.border))
            .title_bottom(
                Line::from(format!(
                    " {} / {} ",
                    if fields.is_empty() {
                        0
                    } else {
                        selected + 1
                    },
                    fields.len()
                ))
                .right_aligned(),
            ),
    );
    table_state.select(if fields.is_empty() {
        None
    } else {
        Some(selected)
    });
    frame.render_stateful_widget(table, content_areas[0], table_state);
    let viewports = if let Some(area) = content_areas.get(1) {
        render_report_tables(frame, screen.tables, screen.table_offset, *area, theme)
    } else {
        vec![]
    };
    if !screen.errors.is_empty() {
        let lines: Vec<Line> = screen
            .errors
            .iter()
            .map(|error| Line::from(clean(error)))
            .collect();
        frame.render_widget(
            Paragraph::new(lines)
                .style(Style::default().fg(theme.error))
                .block(Block::bordered().title(" Resolve before submitting ")),
            sections[2],
        );
    }
    if let Some(editor) = &screen.editor {
        if let Some(date) = editor.calendar {
            render_date_editor(frame, editor, date, theme);
            return viewports;
        }
        if let Some(index) = editor.choice {
            let parts =
                Layout::vertical([Constraint::Min(3), Constraint::Length(2)]).split(sections[3]);
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
                Paragraph::new(if editor.constructor {
                    "↑/↓ or j/k choose · Enter switch · Esc cancel · Drafts kept"
                } else {
                    "↑/↓ or j/k choose · Enter save · Esc cancel"
                })
                .wrap(ratatui::widgets::Wrap { trim: true })
                .style(Style::default().fg(theme.subtext)),
                parts[1],
            );
            return viewports;
        }
        let parts = Layout::vertical([
            Constraint::Length(3),
            Constraint::Length(1),
            Constraint::Length(2),
        ])
        .split(sections[3]);
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
            Paragraph::new(
                if fields
                    .get(selected)
                    .is_some_and(|f| f.presentation.text)
                {
                    "Read-only · ↑/↓ select · q submit · x cancel"
                } else if fields
                    .get(selected)
                    .is_some_and(|f| f.presentation.computed)
                {
                    "Computed · ↑/↓ select · q submit · x cancel"
                } else if fields
                    .get(selected)
                    .is_some_and(|f| f.presentation.disabled)
                {
                    "Disabled · ↑/↓ select · q submit · x cancel"
                } else if fields
                    .get(selected)
                    .is_some_and(|f| f.presentation.constructor || f.presentation.choice)
                {
                    "↑/↓ select · Enter choose · q submit · x cancel"
                } else if fields.get(selected).is_some_and(|f| f.action) {
                    "↑/↓ select · Enter activate · q submit · x cancel"
                } else {
                    "↑/↓ select · Enter edit · Space toggle · q submit · x cancel"
                },
            )
            .style(Style::default().fg(theme.subtext))
            .wrap(ratatui::widgets::Wrap { trim: true })
            .block(
                Block::default()
                    .borders(Borders::TOP)
                    .border_style(Style::default().fg(theme.border)),
            ),
            sections[3],
        );
    }
    viewports
}

fn render_date_editor(frame: &mut Frame, editor: &Editor<'_>, date: NaiveDate, theme: Theme) {
    let area = frame.area();
    let width = area.width.min(60);
    let height = area.height.min(18);
    let popup = Rect::new(
        area.x + (area.width - width) / 2,
        area.y + (area.height - height) / 2,
        width,
        height,
    );
    frame.render_widget(Clear, popup);
    let block = Block::bordered()
        .title(format!(" {} ", clean(editor.label)))
        .style(Style::default().fg(theme.text).bg(theme.base))
        .border_style(Style::default().fg(theme.accent));
    let inner = block.inner(popup);
    frame.render_widget(block, popup);
    let parts = Layout::vertical([
        Constraint::Length(if height < 16 { 1 } else { 3 }),
        Constraint::Min(0),
        Constraint::Length(1),
        Constraint::Length(4),
    ])
    .split(inner);
    frame.render_widget(
        Paragraph::new(format!(
            "{}{}",
            editor_tail(&clean(editor.text), parts[0].width.saturating_sub(3)),
            if editor.date_input { "▏" } else { "" }
        ))
        .block(
            (if parts[0].height > 1 {
                Block::bordered().title(" YYYY-MM-DD ")
            } else {
                Block::default()
            })
            .border_style(Style::default().fg(if editor.error.is_some() {
                theme.error
            } else {
                theme.accent
            })),
        ),
        parts[0],
    );
    let mut lines = vec![
        Line::styled(
            date.format("%B %Y").to_string(),
            Style::default()
                .fg(theme.accent)
                .add_modifier(Modifier::BOLD),
        ),
        Line::styled(" Mo Tu We Th Fr Sa Su", Style::default().fg(theme.subtext)),
    ];
    let offset = date.with_day(1).unwrap().weekday().num_days_from_monday();
    for week in 0..6 {
        let mut cells = Vec::new();
        for weekday in 0..7 {
            let position = week * 7 + weekday;
            let day = position as i32 - offset as i32 + 1;
            let valid =
                day > 0 && NaiveDate::from_ymd_opt(date.year(), date.month(), day as u32).is_some();
            let style = if valid && day as u32 == date.day() {
                Style::default()
                    .fg(theme.text)
                    .bg(theme.selection)
                    .add_modifier(Modifier::BOLD)
            } else {
                Style::default().fg(theme.text)
            };
            cells.push(Span::styled(
                if valid {
                    format!("{day:>3}")
                } else {
                    "   ".into()
                },
                style,
            ));
        }
        lines.push(Line::from(cells));
    }
    // In short terminals, keep the selected week in view with its heading.
    if parts[1].height < lines.len() as u16 && parts[1].height > 2 {
        let selected_week = ((offset + date.day() - 1) / 7) as usize;
        let visible_weeks = parts[1].height as usize - 2;
        let start = (selected_week + 1).saturating_sub(visible_weeks);
        lines = lines[..2]
            .iter()
            .cloned()
            .chain(lines[2 + start..].iter().take(visible_weeks).cloned())
            .collect();
    }
    frame.render_widget(
        Paragraph::new(lines).alignment(ratatui::layout::Alignment::Center),
        parts[1],
    );
    let invalid_text = editor.text.trim() != date.to_string();
    frame.render_widget(
        Paragraph::new(editor.error.as_deref().unwrap_or(if invalid_text {
            "Calendar shows the last valid date."
        } else {
            ""
        }))
        .style(Style::default().fg(if editor.error.is_some() {
            theme.error
        } else {
            theme.subtext
        })),
        parts[2],
    );
    frame.render_widget(Paragraph::new(if editor.date_input {
        "INPUT · YYYY-MM-DD\nCtrl-U clear · Backspace delete\nEnter save\nEsc back to calendar"
    } else {
        "CALENDAR · h/l day · k/j week\nArrows move · PgUp/PgDn month\ni / Enter edit input\nEsc cancel"
    })
        .style(Style::default().fg(theme.subtext)).wrap(ratatui::widgets::Wrap { trim: true }), parts[3]);
}

#[cfg(test)]
mod tests;
