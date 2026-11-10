//! tlapm's method pragmas: the new `(*{ by (prover:"zenon"; timeout:@) }*)` after a definition,
//! which `E_parser.read_new_method` reads into a Bpragma, and the old `(*{ by (zenon) }*)` of
//! Method_prs. A port of `src/obligations/pragma.ts`.

#[derive(Clone, Debug, PartialEq)]
pub enum PragmaValue {
    Default,
    String(String),
    Float(f64),
}

#[derive(Clone, Debug, PartialEq)]
pub struct PragmaSetting {
    pub hint: String,
    pub value: PragmaValue,
}

/// An old-style method, with the tactic an isabelle method takes and the timeout in seconds an
/// isabelle or zenon method may take.
#[derive(Clone, Debug, PartialEq)]
pub struct OldMethod {
    pub name: String,
    pub tactic: Option<String>,
    pub timeout: Option<f64>,
}
