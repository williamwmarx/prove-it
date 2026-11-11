# Pending: unit cases of SANY's report

Each directory holds one case from `tests/unit/sany-report.test.ts` where tla-front's report and the
TypeScript report's expectation disagree. `case.json` names the root module and TLC's version.

Record each with real TLC, in a copy of its directory, with an empty `<root>.cfg`:

    java -cp <tla2tools> tlc2.TLC -nowarning -noGenerateSpecTE -workers 1 -fp 0 -seed 0 <root>

with the d8fb231 jar where `version` is `master`, and TLC 1.7.4's
(`native/crates/prove-it-check/fixtures/tla2tools-1.7.4.jar`) where it is `1.7.4`. Record stdout,
stderr and the exit code per directory, as `grid.json` does, keyed `pending-report/<NN>`.
