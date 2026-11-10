//! The size TLC reports of the behavior graphs as it checks the temporal properties part way
//! through the search and at its end, against TLC built at d8fb231.

use std::process::{Command, Output};

// A grid the search finds a diagonal at a time, with a property whose tableau keeps a node for
// every state, one without a tableau, and one whose tableau has a node for the initial state only.
const GRID: &str = "---- MODULE Grid ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\\ y = 0
Next == \\/ x' = (x + 1) % 30 /\\ UNCHANGED y
        \\/ y' = (y + 1) % 30 /\\ UNCHANGED x
Spec == Init /\\ [][Next]_<<x, y>> /\\ WF_<<x, y>>(Next)
Tableau == <>(x = 29 \\/ y = 29)
Plain == []<>(x >= 0)
Initial == <>(x # 0 \\/ y # 0)
====
";

// Checks the grid's properties after `at` states are expanded, on `threads` threads, and returns
// the line TLC prints as it starts the check, up to its time.
fn check_grid(name: &str, properties: &str, at: usize, threads: usize) -> String {
    let directory = std::env::temp_dir().join(format!(
        "prove-it-cli-liveness-{name}-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    let config = format!("SPECIFICATION Spec\nPROPERTY {properties}\nCHECK_DEADLOCK FALSE\n");
    for (file, contents) in [("Grid.tla", GRID), ("Grid.cfg", &config)] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-workers", "4", "-noTE", "Grid"])
        .current_dir(&directory)
        .env("PROVE_IT_TEST_LIVE_CHECK_AT", at.to_string())
        .env("PROVE_IT_WORKERS", threads.to_string())
        .env("PROVE_IT_SHARED_LEVEL", "1")
        .output()
        .expect("the binary runs");
    std::fs::remove_dir_all(directory).expect("removed");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    text.lines()
        .find(|line| line.contains("for the current state space"))
        .and_then(|line| line.split(" at (").next())
        .unwrap_or_else(|| panic!("a check part way through the search: {text}"))
        .to_owned()
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn current(branches: &str, states: usize) -> String {
    format!(
        "Checking {branches}temporal properties for the current state space with {states} total distinct states"
    )
}

#[test]
fn counts_the_behavior_graphs_states_as_tlc_does_part_way_through_the_search() {
    // After 50 states, the first 45 of diagonals 0 to 8 and 5 of the 10 of diagonal 9, the search
    // has found 61, which are queued as far as the 11 of diagonal 10 that the 5 reached. TLC
    // counts the states its behavior graphs have a key for (AbstractDiskGraph#size), summed over
    // the branches (LiveCheck.check0): with a tableau, the states expanded and those with a node
    // recorded, such as every successor here; without one, the states expanded; and where only
    // the initial state is consistent with the tableau, the states expanded.
    assert_eq!(check_grid("tableau", "Tableau", 50, 1), current("", 61));
    assert_eq!(check_grid("plain", "Plain", 50, 1), current("", 50));
    assert_eq!(check_grid("initial", "Initial", 50, 1), current("", 50));
    assert_eq!(
        check_grid("two", "Tableau Plain", 50, 1),
        current("2 branches of ", 111)
    );
    assert_eq!(
        check_grid("three", "Tableau Plain Initial", 50, 1),
        current("3 branches of ", 161)
    );
    // On threads, which build the branches' graphs apart.
    assert_eq!(check_grid("shared", "Tableau", 50, 4), current("", 61));
    assert_eq!(
        check_grid("shared-three", "Tableau Plain Initial", 50, 4),
        current("3 branches of ", 161)
    );
}

#[test]
fn counts_the_successor_left_on_the_queue_of_a_chain() {
    // TLC's count is the distinct states found, the one queued among them.
    let spec = "---- MODULE Chain ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 100 /\\ x' = x + 1\nSpec == Init /\\ [][Next]_x /\\ WF_x(Next)\nLive == <>(x = 100)\n====\n";
    let directory = std::env::temp_dir().join(format!(
        "prove-it-cli-liveness-chain-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (file, contents) in [
        ("Chain.tla", spec),
        (
            "Chain.cfg",
            "SPECIFICATION Spec\nPROPERTY Live\nCHECK_DEADLOCK FALSE\n",
        ),
    ] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-workers", "1", "-nowarning", "-noTE", "Chain"])
        .current_dir(&directory)
        .env("PROVE_IT_TEST_LIVE_CHECK_AT", "10")
        .output()
        .expect("the binary runs");
    std::fs::remove_dir_all(directory).expect("removed");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains(&format!("{} at (", current("", 11))),
        "{text}"
    );
    assert!(
        text.contains("Checking temporal properties for the complete state space with 101 total distinct states at ("),
        "{text}"
    );
}
