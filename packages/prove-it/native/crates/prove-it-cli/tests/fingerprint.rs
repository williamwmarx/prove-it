//! Runs the binary with -fp N, against what TLC at d8fb231 prints with the same -fp.

mod common;

use common::{run, stdout};

// What depends on the polynomial -fp picks: TLCGet("config").fingerprint, TLCFP, the draws of
// RandomElement, which TLC seeds with each state's fingerprint, and the estimate from the actual
// fingerprints. Each is what TLC at d8fb231 prints with that -fp.
#[test]
fn fingerprints_with_the_polynomial_fp_picks() {
    let directory = std::env::temp_dir().join(format!("prove-it-cli-fp-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (name, spec, config) in [
        (
            "Grid",
            "---- MODULE Grid ----\nEXTENDS Naturals, TLC, TLCExt\nVARIABLES x, y\nASSUME PrintT(TLCGet(\"config\").fingerprint)\nASSUME PrintT(TLCFP(<<1, \"a\", {2, 3}>>))\nInit == x = 0 /\\ y = 0\nNext == \\/ x' = (x + 1) % 320 /\\ y' = y\n        \\/ y' = (y + 1) % 320 /\\ x' = x\n        \\/ UNCHANGED <<x, y>>\n====\n",
            "INIT Init\nNEXT Next\n",
        ),
        (
            "Draws",
            "---- MODULE Draws ----\nEXTENDS Naturals, TLC\nVARIABLES x, r\nInit == x = 0 /\\ r = 0\nNext == x < 3 /\\ x' = x + 1 /\\ r' = RandomElement(1..1000000)\nSmall == x < 3\n====\n",
            "INIT Init\nNEXT Next\nINVARIANT Small\n",
        ),
    ] {
        std::fs::write(directory.join(format!("{name}.tla")), spec).expect("a spec");
        std::fs::write(directory.join(format!("{name}.cfg")), config).expect("a configuration");
    }
    for (index, polynomial, value, actual, draws) in [
        (
            "1",
            "-2699332217222594175",
            "641489468",
            "1.6E-13",
            ["267355", "930227", "103044"],
        ),
        (
            "10",
            "-4882326079550032221",
            "-697347947",
            "1.5E-13",
            ["122111", "453114", "660192"],
        ),
        (
            "130",
            "-7929249073132661339",
            "1794742668",
            "1.0E-13",
            ["642118", "175135", "307483"],
        ),
    ] {
        let grid = run(&directory, &["-nowarning", "-noTE", "-fp", index, "Grid"]);
        let text = stdout(&grid);
        assert_eq!(grid.status.code(), Some(0), "{text}");
        assert!(
            text.contains(&format!(
                "Running breadth-first search Model-Checking with fp {index} and seed "
            )),
            "{text}"
        );
        assert!(
            text.contains(&format!(
                "\n\"{polynomial}\"\n{value}\nComputing initial states...\n"
            )),
            "{text}"
        );
        assert!(
            text.contains(&format!(
                "Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 1.1E-9
  based on the actual fingerprints:  val = {actual}
307201 states generated, 102400 distinct states found, 0 states left on queue.
"
            )),
            "{text}"
        );
        let drawn = run(
            &directory,
            &["-nowarning", "-noTE", "-seed", "0", "-fp", index, "Draws"],
        );
        let text = stdout(&drawn);
        assert_eq!(drawn.status.code(), Some(12), "{text}");
        let [first, second, third] = draws;
        assert!(
            text.contains(&format!(
                "State 1: <Initial predicate>
/\\ r = 0
/\\ x = 0

State 2: <Next line 5, col 9 to line 5, col 61 of module Draws>
/\\ r = {first}
/\\ x = 1

State 3: <Next line 5, col 9 to line 5, col 61 of module Draws>
/\\ r = {second}
/\\ x = 2

State 4: <Next line 5, col 9 to line 5, col 61 of module Draws>
/\\ r = {third}
/\\ x = 3

4 states generated, 4 distinct states found, 0 states left on queue.
"
            )),
            "{text}"
        );
    }
    std::fs::remove_dir_all(directory).expect("removed");
}
