//! # OpenRouter advisor adapter — Socratic ATS2 programming coach
//!
//! *Literate note.*  This adapter connects the REPL to OpenRouter's API
//! to provide Socratic critiques, type invariant explanations, and guidance
//! on compiler errors **without ever writing the code for the user**.
//!
//! By default, it routes to OpenRouter's free models (`openrouter/auto` or
//! `meta-llama/llama-3.3-70b-instruct:free`), configurable via `OPENROUTER_MODEL`.
//! API keys are read from `OPENROUTER_API_KEY`.

use std::process::Command;

use ats2_application::ports::{AdvisorContext, AdvisorPort};

const DEFAULT_MODEL: &str = "openrouter/auto";

const SYSTEM_PROMPT: &str = "\
You are an expert ATS2 (Applied Type System) programming mentor and coach.
Your mission is to teach the user to 'THINK in ATS2' and adopt a 'Commit-First' (specification and type invariant first) approach before jumping into implementations.

PEDAGOGICAL & COACHING PRINCIPLES:
1. COMMIT-FIRST DISCIPLINE:
   - Teach the user to define their types, sorts, invariants, pre/post-conditions, and theorem proofs BEFORE writing the dynamic function bodies.
   - When a user asks for help or encounters an error, first ask: 'What are the static properties and invariants you want to commit to?'
2. THINK IN ATS2 (STATIC vs DYNAMIC):
   - Reinforce the fundamental divide: Statics (types, sorts, props, proofs) exist only for verification and are completely erased at runtime. Dynamics (expressions, values, effects) compute at runtime.
   - Guide the user to structure their mental model around:
     a) Sorts & Invariants: {n: nat | n >= 0}
     b) Linear views & resources: (view @ L | ptr(L))
     c) Proof commitments (prfn, prval) and termination metrics (<n>).
3. SOCRATIC COACHING:
   - NEVER output the completed solution code or give away copy-paste snippets.
   - NEVER write the implementation for the user.
   - Ask leading questions that prompt the user to reflect on constraints, edge cases (e.g. n = 0, empty list, consumed resource), or mismatched sorts.
4. SYNTAX & SUBTLETY GUIDANCE:
   - Point out ATS2 syntax rules Socratically:
     - Explicit return types: `fun foo(x: int): int = ...` (omitting `: type` defaults to `ptr`).
     - Punctuation: `:` specifies type/sort annotation, while `=` begins the body expression.
     - Quantifiers and brackets: `{...}` for universal static quantifiers, `[...]` for existential unpacking.
5. Keep guidance concise, insightful, encouraging, and focused on building true ATS2 intuition.
";

/// Connects to OpenRouter's chat completion endpoint via host curl.
#[derive(Debug, Default, Clone)]
pub struct OpenRouterAdvisor {
    model: Option<String>,
}

impl OpenRouterAdvisor {
    pub fn new() -> Self {
        Self { model: None }
    }

    pub fn with_model(model: impl Into<String>) -> Self {
        Self {
            model: Some(model.into()),
        }
    }

    fn resolved_model(&self) -> String {
        if let Some(m) = &self.model {
            return m.clone();
        }
        if let Ok(m) = std::env::var("OPENROUTER_MODEL") {
            if !m.trim().is_empty() {
                return m.trim().to_string();
            }
        }
        DEFAULT_MODEL.to_string()
    }
}

impl AdvisorPort for OpenRouterAdvisor {
    fn advise(&self, context: &AdvisorContext) -> Result<String, String> {
        let api_key = std::env::var("OPENROUTER_API_KEY").unwrap_or_default();
        let model = self.resolved_model();

        let user_prompt = format_user_prompt(context);
        let request_body = build_json_payload(&model, SYSTEM_PROMPT, &user_prompt);

        let mut cmd = Command::new("curl");
        cmd.arg("-s")
            .arg("-X")
            .arg("POST")
            .arg("https://openrouter.ai/api/v1/chat/completions")
            .arg("-H")
            .arg("Content-Type: application/json")
            .arg("-H")
            .arg("HTTP-Referer: https://github.com/ats2-rustified-to-llvm")
            .arg("-H")
            .arg("X-Title: ats2repl");

        if !api_key.is_empty() {
            cmd.arg("-H").arg(format!("Authorization: Bearer {api_key}"));
        }

        cmd.arg("-d").arg(&request_body);

        let output = cmd
            .output()
            .map_err(|e| format!("failed to invoke curl: {e}"))?;

        if !output.status.success() {
            return Err(format!(
                "curl failed with status {}: {}",
                output.status,
                String::from_utf8_lossy(&output.stderr)
            ));
        }

        let raw_response = String::from_utf8_lossy(&output.stdout);
        extract_content(&raw_response)
    }
}

fn format_user_prompt(context: &AdvisorContext) -> String {
    let mut prompt = String::new();

    if !context.session_source.is_empty() {
        prompt.push_str("### Accumulated Session Source:\n```ats\n");
        prompt.push_str(context.session_source);
        prompt.push_str("\n```\n\n");
    }

    if !context.last_submission.is_empty() {
        prompt.push_str("### Current Submission:\n```ats\n");
        prompt.push_str(context.last_submission);
        prompt.push_str("\n```\n\n");
    }

    if !context.last_errors.is_empty() {
        prompt.push_str("### Compiler Diagnostics / Errors:\n");
        for err in context.last_errors {
            prompt.push_str(&format!("- [{:?}] {}\n", err.kind(), err.message()));
        }
        prompt.push('\n');
    }

    if let Some(query) = context.user_query {
        prompt.push_str("### User Question / Request:\n");
        prompt.push_str(query);
        prompt.push('\n');
    } else if !context.last_errors.is_empty() {
        prompt.push_str("Please explain why this was rejected and what conceptual invariant or quantifier the user should consider (remember: do NOT write the solution code).");
    } else {
        prompt.push_str("Please give a brief Socratic critique of the types and structure (do NOT write code).");
    }

    prompt
}

fn escape_json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 16);
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

fn build_json_payload(model: &str, system: &str, user: &str) -> String {
    format!(
        "{{\"model\":\"{}\",\"messages\":[{{\"role\":\"system\",\"content\":\"{}\"}},{{\"role\":\"user\",\"content\":\"{}\"}}]}}",
        escape_json_str(model),
        escape_json_str(system),
        escape_json_str(user)
    )
}

fn extract_content(json_resp: &str) -> Result<String, String> {
    // Check for API errors
    if json_resp.contains("\"error\":") {
        if let Some(msg_idx) = json_resp.find("\"message\":") {
            let rest = &json_resp[msg_idx + 10..];
            if let Some(start_quote) = rest.find('"') {
                let after = &rest[start_quote + 1..];
                if let Some(end_quote) = find_unescaped_quote(after) {
                    return Err(format!("OpenRouter error: {}", unescape_json(&after[..end_quote])));
                }
            }
        }
        return Err(format!("OpenRouter API error: {json_resp}"));
    }

    // Look for `"content": "..."` inside `choices`
    if let Some(content_idx) = json_resp.find("\"content\":") {
        let rest = &json_resp[content_idx + 10..];
        let trimmed_rest = rest.trim_start();
        if let Some(after_quote) = trimmed_rest.strip_prefix('"') {
            if let Some(end_quote) = find_unescaped_quote(after_quote) {
                return Ok(unescape_json(&after_quote[..end_quote]));
            }
        }
    }

    Err(format!("could not parse response content from OpenRouter: {json_resp}"))
}

fn find_unescaped_quote(s: &str) -> Option<usize> {
    let mut escaped = false;
    for (i, c) in s.char_indices() {
        if escaped {
            escaped = false;
        } else if c == '\\' {
            escaped = true;
        } else if c == '"' {
            return Some(i);
        }
    }
    None
}

fn unescape_json(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('"') => out.push('"'),
                Some('\\') => out.push('\\'),
                Some('n') => out.push('\n'),
                Some('r') => out.push('\r'),
                Some('t') => out.push('\t'),
                Some('u') => {
                    let hex: String = chars.by_ref().take(4).collect();
                    if let Ok(val) = u32::from_str_radix(&hex, 16) {
                        if let Some(ch) = char::from_u32(val) {
                            out.push(ch);
                            continue;
                        }
                    }
                    out.push_str("\\u");
                    out.push_str(&hex);
                }
                Some(other) => {
                    out.push('\\');
                    out.push(other);
                }
                None => out.push('\\'),
            }
        } else {
            out.push(c);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn json_escaping_handles_quotes_and_newlines() {
        let raw = "hello \"world\"\nnext line \\ path";
        let escaped = escape_json_str(raw);
        assert_eq!(escaped, "hello \\\"world\\\"\\nnext line \\\\ path");
    }

    #[test]
    fn response_extractor_pulls_content() {
        let resp = r#"{"id":"gen-123","choices":[{"message":{"role":"assistant","content":"Look at the quantifier."}}]}"#;
        let content = extract_content(resp).expect("extract");
        assert_eq!(content, "Look at the quantifier.");
    }
}
