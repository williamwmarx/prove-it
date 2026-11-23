//! A port of upstream's scripts/tla-ts-backend.ts over Prove It's Rust backends: prints the
//! verdict upstream's harness records for a backend input, run alone with no time limit.
//! Usage: backend-run <z3|zenon|isabelle|ls4> <file>
use prove_decide::{DecideError, Limits};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (backend, path) = (args[0].clone(), args[1].clone());
    let text = std::fs::read_to_string(&path).expect("the input");
    // An SMT-LIB script (.smt2) asks for Z3's whole output, which the port doesn't produce.
    if path.ends_with(".smt2") {
        eprintln!("prove-it: not native yet: an SMT-LIB script, which the port reads only as tlapm writes it");
        std::process::exit(1);
    }
    let result = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let limits = Limits::new(f64::INFINITY, None, None);
            if backend == "zenon" {
                match prove_zenon::decide::run_zenon(&text, &limits) {
                    // A proof the search found and the port's check refused is a decline, as the
                    // CLI's.
                    Ok(run) if run.proof.is_some() && run.isar.is_none() && run.failure.is_none() => {
                        Err(DecideError::Declined("a proof Zenon finds that the port's check refuses".to_owned()))
                    }
                    Ok(run) => match run.isar {
                        Some(isar) => {
                            let start = isar.find("(* BEGIN-PROOF *)\n").map(|i| i + "(* BEGIN-PROOF *)\n".len());
                            let end = isar.find("(* END-PROOF *)");
                            match (start, end) {
                                (Some(s), Some(e)) if s <= e => Ok(format!("unsat\n{}", isar[s..e].trim_end())),
                                _ => Ok("unknown".to_owned()),
                            }
                        }
                        None => Ok("unknown".to_owned()),
                    },
                    Err(error) => Err(DecideError::Prover(error.0)),
                }
            } else {
                // A decision the port couldn't take (stop=unsupported) is a decline, as the CLI's.
                prove_it_prover::decide(&backend, &text, &limits).and_then(|d| {
                    let is_unsupported = d.statistics.iter().any(|(name, value)| {
                        *name == "stop" && matches!(value, prove_decide::Statistic::Text(text) if text == "unsupported")
                    });
                    if is_unsupported {
                        Err(DecideError::Declined(format!("{backend} can't take the input")))
                    } else {
                        Ok(d.verdict.name().to_owned())
                    }
                })
            }
        })
        .expect("a thread")
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
    match result {
        Ok(text) => println!("{text}"),
        Err(DecideError::Prover(message)) => {
            // tla-ts-backend throws a TlaProverError, which ends node with the error on stderr.
            eprintln!("TlaProverError: {message}");
            std::process::exit(1);
        }
        Err(DecideError::Declined(reason)) => {
            eprintln!("prove-it: not native yet: {reason}");
            std::process::exit(1);
        }
    }
}
