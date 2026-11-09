//! What the tests share: the engine's search on a golden IR, stopped where it stops, with the
//! states it kept.

use tla_engine::search::{Reporter, SearchOutcome, Settings, search};
use tla_values::transfer::decode_shared_states;
use tla_values::{Id, Store};

pub struct Quiet;

impl Reporter for Quiet {
    fn initial_states_started(&mut self) {}
    fn initial_states_progress(&mut self, _count: u64) {}
    fn initial_states(&mut self, _generated: u64, _distinct: u64) {}
    fn progress(&mut self, _generated: u64, _distinct: u64, _queued: u64, _depth: u64) {}
    fn print(&mut self, _store: &Store, _values: &[Id]) {}
}

pub fn ir_directory() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../tests/conformance/ir")
}

/// The search's states up to where it stopped, in a store of their own, with their parents, why
/// it stopped and the state it was expanding.
pub struct Stopped {
    pub store: Store,
    pub states: Vec<Vec<Id>>,
    pub parents: Vec<i32>,
    pub reason: String,
    pub expanding: usize,
}

pub fn stop_search(ir: &tla_ir::Ir, stop_at: Option<usize>) -> Option<Stopped> {
    let settings = Settings {
        stop_at,
        ..Settings::default()
    };
    let SearchOutcome::Stopped {
        reason, checkpoint, ..
    } = search(ir, &settings, &mut Quiet)
    else {
        return None;
    };
    let width = ir.variables.len();
    let mut store = Store::new();
    let ranked: Vec<Vec<u16>> = ir.texts[..ir.ranked_count as usize]
        .iter()
        .map(|text| text.encode_utf16().collect())
        .collect();
    store.reset(ranked.iter().map(Vec::as_slice));
    // A search that stops in the initial predicate keeps no state.
    let Some(checkpoint) = checkpoint else {
        return Some(Stopped {
            store,
            states: Vec::new(),
            parents: Vec::new(),
            reason,
            expanding: 0,
        });
    };
    let ids = decode_shared_states(&mut store, &checkpoint.states, width).ok()?;
    let states = if width == 0 {
        Vec::new()
    } else {
        ids.chunks(width).map(<[Id]>::to_vec).collect()
    };
    Some(Stopped {
        store,
        states,
        parents: checkpoint.parents.clone(),
        reason,
        expanding: checkpoint.expanding as usize,
    })
}

pub fn path_to(parents: &[i32], index: usize) -> Vec<usize> {
    let mut path = vec![index];
    while parents[path[0]] >= 0 {
        path.insert(0, parents[path[0]] as usize);
    }
    path
}
