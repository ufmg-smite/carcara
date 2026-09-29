pub mod alethe_2_eunoia;
pub mod alethe_signature;
pub mod ast;
mod printer;

/// A struct that wraps an `EunoiaProof` and implements `fmt::Display`, allowing the proof to be
/// pretty printed.
pub use printer::DisplayEunoiaProof;
