//! # Terminal interactive line reader with history and cursor navigation
//!
//! Implemented in 100% pure standard-library Rust (zero external dependencies).
//! Supports:
//! - Up / Down arrows for session history navigation
//! - Left / Right arrows and Home / End for cursor movement
//! - Backspace and Delete keys
//! - Ctrl+C (cancel line) and Ctrl+D (EOF / exit)
//! - Automatic fallback to cooked/buffered reader when stdin is not a TTY (pipes, tests)

use std::fs::{File, OpenOptions};
use std::io::{self, BufRead, IsTerminal, Read, Write};
use std::path::PathBuf;
use std::process::Command;

/// Interactive line reader managing history and cursor movement.
pub struct LineReader {
    history: Vec<String>,
    history_file: Option<PathBuf>,
}

impl LineReader {
    pub fn new() -> Self {
        let history_file = get_default_history_path();
        let history = load_history(&history_file);
        Self {
            history,
            history_file,
        }
    }

    /// Read a line with prompt and history navigation.
    pub fn read_line<R: BufRead, W: Write>(
        &mut self,
        prompt: &str,
        input: &mut R,
        output: &mut W,
    ) -> io::Result<Option<String>> {
        // If stdin is not a terminal (e.g. tests or piped input), fall back to basic line reading
        if !std::io::stdin().is_terminal() {
            write!(output, "{prompt}")?;
            output.flush()?;
            let mut line = String::new();
            let n = input.read_line(&mut line)?;
            if n == 0 {
                return Ok(None);
            }
            return Ok(Some(line.trim_end_matches(&['\r', '\n'][..]).to_string()));
        }

        // Interactive terminal mode with raw mode
        write!(output, "{prompt}")?;
        output.flush()?;

        let _guard = RawModeGuard::enter();
        let mut stdin = io::stdin();

        let mut buffer: Vec<char> = Vec::new();
        let mut cursor_pos = 0usize;
        let mut history_index = self.history.len();
        let mut current_draft = String::new();

        loop {
            let mut byte = [0u8; 1];
            if stdin.read_exact(&mut byte).is_err() {
                return Ok(None);
            }

            match byte[0] {
                // Enter / Return
                b'\r' | b'\n' => {
                    write!(output, "\r\n")?;
                    output.flush()?;
                    let result: String = buffer.into_iter().collect();
                    if !result.trim().is_empty() {
                        self.add_history(&result);
                    }
                    return Ok(Some(result));
                }
                // Ctrl+D (EOF if empty line)
                4 => {
                    if buffer.is_empty() {
                        write!(output, "\r\n")?;
                        output.flush()?;
                        return Ok(None);
                    } else if cursor_pos < buffer.len() {
                        buffer.remove(cursor_pos);
                        render_line(prompt, &buffer, cursor_pos, output)?;
                    }
                }
                // Ctrl+C (Cancel current line)
                3 => {
                    write!(output, "^C\r\n{prompt}")?;
                    output.flush()?;
                    buffer.clear();
                    cursor_pos = 0;
                    history_index = self.history.len();
                }
                // Ctrl+A (Home)
                1 => {
                    cursor_pos = 0;
                    render_line(prompt, &buffer, cursor_pos, output)?;
                }
                // Ctrl+E (End)
                5 => {
                    cursor_pos = buffer.len();
                    render_line(prompt, &buffer, cursor_pos, output)?;
                }
                // Backspace (ASCII BS or DEL)
                8 | 127 => {
                    if cursor_pos > 0 {
                        cursor_pos -= 1;
                        buffer.remove(cursor_pos);
                        render_line(prompt, &buffer, cursor_pos, output)?;
                    }
                }
                // Tab
                b'\t' => {
                    // Insert 2 spaces
                    buffer.insert(cursor_pos, ' ');
                    buffer.insert(cursor_pos + 1, ' ');
                    cursor_pos += 2;
                    render_line(prompt, &buffer, cursor_pos, output)?;
                }
                // Escape sequence (Arrows, Home, End, Delete)
                0x1b => {
                    let mut seq = [0u8; 2];
                    if stdin.read_exact(&mut seq).is_ok() && seq[0] == b'[' {
                        match seq[1] {
                            // Up Arrow: History backward
                            b'A' => {
                                if !self.history.is_empty() && history_index > 0 {
                                    if history_index == self.history.len() {
                                        current_draft = buffer.iter().collect();
                                    }
                                    history_index -= 1;
                                    buffer = self.history[history_index].chars().collect();
                                    cursor_pos = buffer.len();
                                    render_line(prompt, &buffer, cursor_pos, output)?;
                                }
                            }
                            // Down Arrow: History forward
                            b'B' => {
                                if history_index < self.history.len() {
                                    history_index += 1;
                                    if history_index == self.history.len() {
                                        buffer = current_draft.chars().collect();
                                    } else {
                                        buffer = self.history[history_index].chars().collect();
                                    }
                                    cursor_pos = buffer.len();
                                    render_line(prompt, &buffer, cursor_pos, output)?;
                                }
                            }
                            // Right Arrow
                            b'C' => {
                                if cursor_pos < buffer.len() {
                                    cursor_pos += 1;
                                    render_line(prompt, &buffer, cursor_pos, output)?;
                                }
                            }
                            // Left Arrow
                            b'D' => {
                                if cursor_pos > 0 {
                                    cursor_pos -= 1;
                                    render_line(prompt, &buffer, cursor_pos, output)?;
                                }
                            }
                            // Home
                            b'H' => {
                                cursor_pos = 0;
                                render_line(prompt, &buffer, cursor_pos, output)?;
                            }
                            // End
                            b'F' => {
                                cursor_pos = buffer.len();
                                render_line(prompt, &buffer, cursor_pos, output)?;
                            }
                            // Extended sequences e.g. Delete (3~)
                            b'3' => {
                                let mut last = [0u8; 1];
                                if stdin.read_exact(&mut last).is_ok()
                                    && last[0] == b'~'
                                    && cursor_pos < buffer.len()
                                {
                                    buffer.remove(cursor_pos);
                                    render_line(prompt, &buffer, cursor_pos, output)?;
                                }
                            }
                            _ => {}
                        }
                    }
                }
                // Standard printable characters
                b if b >= 32 => {
                    let ch = b as char;
                    buffer.insert(cursor_pos, ch);
                    cursor_pos += 1;
                    render_line(prompt, &buffer, cursor_pos, output)?;
                }
                _ => {}
            }
        }
    }

    fn add_history(&mut self, line: &str) {
        if self.history.last().map(|s| s.as_str()) != Some(line) {
            self.history.push(line.to_string());
            if let Some(path) = &self.history_file {
                let _ = append_history_file(path, line);
            }
        }
    }
}

fn render_line<W: Write>(
    prompt: &str,
    buffer: &[char],
    cursor_pos: usize,
    output: &mut W,
) -> io::Result<()> {
    let content: String = buffer.iter().collect();
    // \r: return to start of line
    // {prompt}{content}: write full line
    // \x1b[K: clear from cursor to end of line
    // \r: return to start
    // \x1b[<col>C: move cursor to prompt_len + cursor_pos
    let prompt_len = prompt.chars().count();
    let target_col = prompt_len + cursor_pos;

    write!(output, "\r{prompt}{content}\x1b[K\r")?;
    if target_col > 0 {
        write!(output, "\x1b[{}C", target_col)?;
    }
    output.flush()
}

/// RAII Guard that manages raw terminal mode via `stty`.
struct RawModeGuard {
    active: bool,
}

impl RawModeGuard {
    fn enter() -> Self {
        let ok = Command::new("stty")
            .args(["-icanon", "-echo", "min", "1"])
            .status()
            .map(|s| s.success())
            .unwrap_or(false);
        Self { active: ok }
    }
}

impl Drop for RawModeGuard {
    fn drop(&mut self) {
        if self.active {
            let _ = Command::new("stty").arg("sane").status();
        }
    }
}

fn get_default_history_path() -> Option<PathBuf> {
    if let Ok(home) = std::env::var("HOME") {
        Some(PathBuf::from(home).join(".ats2repl_history"))
    } else {
        None
    }
}

fn load_history(path_opt: &Option<PathBuf>) -> Vec<String> {
    let mut history = Vec::new();
    if let Some(path) = path_opt {
        if let Ok(file) = File::open(path) {
            let reader = io::BufReader::new(file);
            for line in reader.lines().flatten() {
                let trimmed = line.trim();
                if !trimmed.is_empty() {
                    history.push(trimmed.to_string());
                }
            }
        }
    }
    history
}

fn append_history_file(path: &PathBuf, line: &str) -> io::Result<()> {
    let mut file = OpenOptions::new().create(true).append(true).open(path)?;
    writeln!(file, "{line}")
}
