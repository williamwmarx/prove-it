# Constant and substitute cases (data only, never merged)

Adversarial inputs from the liveness-atoms session, kept for the startup-definitions model
("TLC computed this at startup and holds this value").

- `round6-cases.tar.gz`: 1,203 cases, one directory each: `M.tla`, `M.cfg`, the other modules
  (`Inner.tla`, `InnerNP.tla`, `Lib.tla`), an optional `root` file, `lib/` or `M.class` for the
  Java-class cases, and `result3.json`. That file holds, per option set, the outputs of the jar,
  main (3bd83eaf) and the old action-constraints branch, at 1 and 4 workers.
- The jar is tla2tools.jar at tlaplus d8fb231, always run with `-noTE`. Without `-noTE`, TLC
  interns `_TLCTrace` and its EXTENDS first, which changes string order; with it, the order
  matches the binaries.
- `round6-classification.txt`: `judge.py all` output.
  - A: main matched and the branch did not.
  - B: main declined and the branch differed.
  - C: the branch differed.
  - Blank: no finding.
- `round6-branch.diff`: the old action-constraints diff these were run against.
- `round6-scripts.tar.gz`: the generators (`gen_*.py`), `run.py` and `judge.py`.
- `rerun-noTE.tar.gz`: rounds 1 to 5 rerun with the jar in `-noTE` mode (`jobs.jsonl`, results
  in `res_*.jsonl`).

Open findings for the startup model (round 6):
- (a) A root-scoped `<-` on a name used directly as CONSTRAINT, ACTION_CONSTRAINT or INVARIANT;
  a name read only by ASSUME.
- (b) A lazy substitute through an INSTANCE whose body is EXCEPT, LET, an operator application or
  recursive; a record substitute in an action constraint; a parameter-free INSTANCE printing its
  startup PrintT twice.
- (c) `X <- Y` where Y is bound by value; `INVARIANT V` with `V = TRUE`; the root `.class` on the
  library path.
