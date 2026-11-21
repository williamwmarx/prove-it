//! TLC's `TransitiveClosure.Warshall` on written relations.

use std::process::Command;

#[test]
fn warshall_override_and_unproven_inputs() {
    for (name, expr, exit, expected) in [
        (
            "chain",
            "Warshall({<<1, 2>>, <<2, 3>>}) = {<<1, 2>>, <<2, 3>>, <<1, 3>>}",
            0,
            "Model checking completed. No error has been found.",
        ),
        (
            "iteration_order",
            "PrintT({e \\in Warshall({<<1,100>>,<<100,3>>,<<2,0>>}): PrintT(e)})",
            0,
            "<<1, 3>>\n<<1, 100>>\n<<2, 0>>\n<<100, 3>>",
        ),
        (
            "bad_tuple",
            "Warshall({<<1, 2>>, <<3>>}) = {}",
            10,
            "Attempted to apply TransitiveClosure to a set containing\nthe following value:\n<<3>>",
        ),
        (
            "mixed",
            "Warshall({<<1, \"a\">>, <<\"a\", 2>>}) = {}",
            10,
            "but it produced the following error:\nAttempted to compare string \"a\" with non-string:\n1",
        ),
    ] {
        for workers in ["1", "4"] {
            let directory = std::env::temp_dir().join(format!(
                "prove-it-warshall-{name}-{workers}-{}",
                std::process::id()
            ));
            std::fs::create_dir_all(&directory).expect("a directory");
            std::fs::write(
                directory.join("TransitiveClosure.tla"),
                "---- MODULE TransitiveClosure ----\nWarshall(R) == 123\n====\n",
            )
            .expect("the module");
            std::fs::write(
                directory.join("M.tla"),
                format!(
                    "---- MODULE M ----\nEXTENDS TransitiveClosure, TLC\nASSUME {expr}\n====\n"
                ),
            )
            .expect("the spec");
            std::fs::write(directory.join("M.cfg"), "").expect("the config");
            let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                .args(["-workers", workers, "-noGenerateSpecTE", "M"])
                .current_dir(&directory)
                .output()
                .expect("the checker");
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert_eq!(
                output.status.code(),
                Some(exit),
                "{name}: {stdout}\n{stderr}"
            );
            assert!(
                stdout.contains(expected) || stderr.contains(expected),
                "{name}: {stdout}\n{stderr}"
            );
            std::fs::remove_dir_all(directory).expect("removed");
        }
    }
}
