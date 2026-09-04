//! Reads `custom_operators.toml` and generates `$OUT_DIR/custom_operators.rs` at build time.

use std::fmt::Write as _;

/// One `[[operator]]` entry parsed from the config file.
struct OperatorEntry {
    name: String,
    return_type: String,
    arg_types: Vec<String>,
}

/// Maps a supported sort name to its `Sort` variant token, or `None` if unsupported.
fn sort_token(name: &str) -> Option<&'static str> {
    match name {
        "Bool" => Some("Sort::Bool"),
        "Int" => Some("Sort::Int"),
        "Real" => Some("Sort::Real"),
        "String" => Some("Sort::String"),
        "RegLan" => Some("Sort::RegLan"),
        _ => None,
    }
}

/// Strips a `"..."` quoted string, panicking with `context` on malformed input.
fn parse_quoted_string(value: &str, context: &str) -> String {
    let value = value.trim();
    let inner = value
        .strip_prefix('"')
        .and_then(|s| s.strip_suffix('"'))
        .unwrap_or_else(|| panic!("{context}: expected a quoted string, got `{value}`"));
    inner.to_string()
}

/// Parses a `["a", "b", ...]` list of quoted strings, panicking with `context` on malformed input.
fn parse_string_list(value: &str, context: &str) -> Vec<String> {
    let value = value.trim();
    let inner = value
        .strip_prefix('[')
        .and_then(|s| s.strip_suffix(']'))
        .unwrap_or_else(|| panic!("{context}: expected a `[...]` list, got `{value}`"));
    let inner = inner.trim();
    if inner.is_empty() {
        return Vec::new();
    }
    inner
        .split(',')
        .map(|s| parse_quoted_string(s, context))
        .collect()
}

/// Parses one `[[operator]]` chunk (the text following the `[[operator]]` marker, up to the next
/// one) into an `OperatorEntry`.
fn parse_operator_chunk(chunk: &str) -> OperatorEntry {
    let mut name = None;
    let mut return_type = None;
    let mut arg_types = None;

    for line in chunk.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (key, value) = line
            .split_once('=')
            .unwrap_or_else(|| panic!("malformed line in custom_operators.toml: `{line}`"));
        let key = key.trim();
        let value = value.trim();
        match key {
            "name" => name = Some(parse_quoted_string(value, "`name`")),
            "return_type" => return_type = Some(parse_quoted_string(value, "`return_type`")),
            "arg_types" => arg_types = Some(parse_string_list(value, "`arg_types`")),
            other => panic!("unknown key `{other}` in custom_operators.toml"),
        }
    }

    let name = name.unwrap_or_else(|| panic!("an [[operator]] entry is missing `name`"));
    let return_type = return_type
        .unwrap_or_else(|| panic!("[[operator]] entry `{name}` is missing `return_type`"));
    let arg_types = arg_types.unwrap_or_default();

    OperatorEntry { name, return_type, arg_types }
}

fn main() {
    println!("cargo:rerun-if-changed=custom_operators.toml");
    println!("cargo:rerun-if-changed=build.rs");

    let content = std::fs::read_to_string("custom_operators.toml")
        .expect("failed to read custom_operators.toml");

    // Drop comment/blank lines first, then split on `[[operator]]` marker lines, so a marker
    // string mentioned inside a comment doesn't get mistaken for a real table-array marker.
    let stripped: String = content
        .lines()
        .filter(|line| {
            let line = line.trim();
            !(line.is_empty() || line.starts_with('#'))
        })
        .collect::<Vec<_>>()
        .join("\n");
    let mut chunks = stripped.split("[[operator]]");
    chunks.next();

    let mut entries = Vec::new();
    let mut seen_names = std::collections::HashSet::new();
    for chunk in chunks {
        let entry = parse_operator_chunk(chunk);
        if !seen_names.insert(entry.name.clone()) {
            panic!("duplicate custom operator name `{}`", entry.name);
        }
        entries.push(entry);
    }

    let mut generated = String::new();
    generated.push_str("pub static CUSTOM_OPERATORS: &[CustomOperatorDef] = &[\n");
    for entry in &entries {
        let return_sort = sort_token(&entry.return_type).unwrap_or_else(|| {
            panic!(
                "unknown sort `{}` for custom operator `{}`",
                entry.return_type, entry.name
            )
        });
        let arg_sorts: Vec<&str> = entry
            .arg_types
            .iter()
            .map(|arg| {
                sort_token(arg).unwrap_or_else(|| {
                    panic!("unknown sort `{arg}` for custom operator `{}`", entry.name)
                })
            })
            .collect();
        writeln!(
            generated,
            "    CustomOperatorDef {{ name: {:?}, arg_sorts: &[{}], return_sort: {} }},",
            entry.name,
            arg_sorts.join(", "),
            return_sort,
        )
        .unwrap();
    }
    generated.push_str("];\n");

    let out_dir = std::env::var("OUT_DIR").expect("OUT_DIR not set");
    let out_path = std::path::Path::new(&out_dir).join("custom_operators.rs");
    std::fs::write(out_path, generated).expect("failed to write custom_operators.rs");
}
