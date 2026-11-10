# TLC recordings (scratch, not for merge)

Raw TLC output for two small spec sets. Nothing in the `.out`, `.err` or
`.exit` files has been edited.

- TLC: `tla2tools.jar` built from tlaplus commit `d8fb231`, run on OpenJDK 21.0.12.1.
- Invocation, from inside the spec's own directory:
  `java -cp tla2tools.jar tlc2.TLC <options> -config <name>.cfg <name>.tla`
  with `JAVA_TOOL_OPTIONS` unset, so the JVM's "Picked up JAVA_TOOL_OPTIONS"
  banner is absent from stderr.
- Files per run: `<name>.<suffix>.out` (stdout), `.err` (stderr),
  `.exit` (exit code).

| Directory | Specs | Options | Suffix |
| --- | --- | --- | --- |
| `lazy-assume/` | Lazy01..Lazy11 | `-noGenerateSpecTE -workers 1` | `w1` |
| `lazy-assume/` | Lazy01..Lazy11 | `-tool -noGenerateSpecTE -workers 1` | `tool.w1` |
| `fingerprint/` | Cell01..Cell10 | `-nowarning -fp 0 -lncheck final -noGenerateSpecTE -workers 1` | `w1` |
| `fingerprint/` | Cell01..Cell10 | `-nowarning -fp 0 -lncheck final -noGenerateSpecTE -workers 4` | `w4` |

All `.err` files are empty.

## Machine-specific lines to normalise

These stdout lines vary by machine, run or time:

- `TLC2 Version 2026.11.10.112638 (rev: ${git.shortRevision})`: the version is
  the local build timestamp, and the revision placeholder was not filled in by
  the local build.
- `Running breadth-first search Model-Checking with fp N and seed S with W
  worker(s) on C cores with H MB heap and O MB offheap memory [pid: P] (OS,
  JVM, ...)`: in `lazy-assume/` the `fp` index is random (no `-fp` given). The
  seed, pid, core count, heap sizes, kernel and JVM versions vary in every file.
  The worker count differs between `w1` and `w4` by design.
- `Parsing file <abs path>/<dir>/<Name>.tla`: the spec's absolute path on the
  recording machine.
- `Parsing file /tmp/tlc-<random>/<Std>.tla (jar:file:<abs path to jar>!/tla2sany/StandardModules/<Std>.tla)`:
  a random temp directory and the jar's absolute path, for each standard module.
- `Starting... (YYYY-MM-DD HH:MM:SS)`: timestamp.
- `Finished computing initial states: ... generated at YYYY-MM-DD HH:MM:SS.`:
  timestamp.
- `Progress(N) at YYYY-MM-DD HH:MM:SS: ... (N s/min) ... (N ds/min) ...`:
  timestamp and rates (only in `-tool` runs).
- `Finished in <duration> at (YYYY-MM-DD HH:MM:SS)`: duration (`00s`, `01s`
  or `NNNms`) and timestamp.

After normalising those lines, every `fingerprint/*.w1.out` matches its
`*.w4.out` exactly.
