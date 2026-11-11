# Regression set for substituted constants and override-index reads

The 13,067 adversarial specs of #292's rounds 1 to 7, for winning back what #292 returned to
main's behaviour. `front-constants-full` holds the implementation that declines them.

`round<N>.tar.gz` holds `round<N>/<case>/`, each with the spec (`M.tla`, `M.cfg` and
the modules and classes beside it) and the outputs at 1 and 4 workers: `tlc<W>.out` and
`tlc<W>.exit` from TLC at d8fb231 (`-fp 0 -nowarning -noGenerateSpecTE`), and `main<W>.*` from
main 40009ac8. A `-simulate` case differs from TLC only in the "Running Random Simulation" banner.

Groups:

- register readers (TLCSet, TLCGet of a register, TLCGetAndSet, TLCGetOrDefault)
- TLCGet("level") printers
- invisible override reads (a TLCOverrides index's method read where the run computes it)
- random draws (RandomElement and the other draws in a substitute)
- final methods (a `final` zero-arity method TLC calls as it loads it)
- VIEW and POSTCONDITION reads
- recursive-operator arguments (TLC passes them unevaluated)

Classification files, one line per case:

- `round<N>.main.txt`: main 40009ac8 against TLC at 1 and 4 workers: `OK` (byte-identical after
  the timing lines), `DECL` (declined) or `BAD` (other output).
- `round<N>.full-branch.txt` (rounds 1 to 6): the same for `front-constants-full` (db2e0de3) as
  `br=`, with `REGRESSION` where main matched and the branch didn't, and `WRONG` where the branch
  printed other output.

Data for another session; never merged.
