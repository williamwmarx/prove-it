//! Prove It's front end in Rust: from `.tla` and `.cfg` files to the engine IR, or to the
//! messages SANY and TLC print, as the TypeScript front end does. DESIGN.md section 14 plans it.

pub mod ast;
pub mod config;
pub mod dependencies;
pub mod describe;
pub mod dump;
pub mod environment;
pub mod errors;
pub mod eval;
pub mod hash;
pub mod instances;
pub mod java_overrides;
pub mod json;
pub mod levels;
pub mod lexer;
pub mod linter;
pub mod live;
pub mod lower;
pub mod model;
pub mod order;
pub mod ordered_map;
pub mod parser;
pub mod pcal;
pub mod recursive;
pub mod report;
pub mod resolve;
pub mod sany;
pub mod sany_parse_error;
pub mod spec;
#[rustfmt::skip]
pub mod standard_builtins;
pub mod standard_modules;
pub mod startup;
pub mod subexpressions;
#[rustfmt::skip]
pub mod tlc_data;
pub mod tlc_messages;
pub mod values;

/// The version of TLC whose behaviour the front end reproduces, as `TlcVersion` in
/// `src/tlc/version.ts`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TlcVersion {
    Master,
    V1_7_4,
}

/// The text of a standard module of SANY in this version of TLC.
pub fn get_standard_module(name: &str, version: TlcVersion) -> Option<&'static str> {
    let modules = match version {
        TlcVersion::Master => standard_modules::MASTER,
        TlcVersion::V1_7_4 => standard_modules::TLC_174,
    };
    modules
        .iter()
        .find(|module| module.0 == name)
        .map(|module| module.1)
}
