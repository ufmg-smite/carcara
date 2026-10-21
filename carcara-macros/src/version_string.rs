use proc_macro::TokenStream;
use quote::quote;
use std::process::Command;
use syn::parse_macro_input;

pub fn version_string(input: TokenStream) -> TokenStream {
    parse_macro_input!(input as syn::parse::Nothing); // error if we are given args

    let version = std::env::var("CARGO_PKG_VERSION").expect("couldn't get package version");
    let hash = run_git(&["describe", "--always"]);
    let branch = run_git(&["rev-parse", "--abbrev-ref", "HEAD"]).filter(|b| b != "HEAD");

    let full_string = match (hash, branch) {
        (None, _) => version.to_owned(),
        (Some(hash), None) => format!("{} [git {}]", version, hash),
        (Some(hash), Some(branch)) => format!("{} [git {} {}]", version, hash, branch),
    };
    quote! { #full_string }.into()
}

/// Run `git` on the manifest directory with the given arguments, and return its output.
fn run_git(args: &[&str]) -> Option<String> {
    let manifest_dir = std::env::var_os("CARGO_MANIFEST_DIR")?;
    let output = Command::new("git")
        .arg("-C")
        .arg(manifest_dir)
        .args(args)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .and_then(|c| c.wait_with_output())
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let mut stdout = output.stdout;
    if stdout.last().copied() == Some(b'\n') {
        stdout.pop();
    }
    String::from_utf8(stdout).ok()
}
