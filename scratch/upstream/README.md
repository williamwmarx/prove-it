# Upstream conformance: startup-guards vs main

Scratch measurement data. This branch is never merged.

## Inputs

- Upstream suite: aidenybai/tla-ts at 28c823e4b680889fbadf4511fbc112f0a9cba419 (HEAD on 2026-11-12), `packages/conformance/test`, suite `tlc`: 61,409 tests, 72,827 runs (the historical count).
- Baseline: prove-it cb48b6ebb4254f7ca40a180cc2e69f70f4e8ef7f, `cargo build --release --locked -p prove-it-cli`, binary sha256 5be1897b957fe6c0e86d0582a84776a20603ada2dc3f3a89f09bc0cf95e00db3.
- Candidate (`startup-guards`): ef8d0a55a378973b94c9a3007742719a351c4166, binary sha256 6e4b020568ac107b9da4fec7f0cd6162cf8de068857ab4f75f4cd2b6e467ea06.
- Pinned TLC: tlaplus/tlaplus d8fb231de4e4b5d02c1b2ed1ac759c086f694021 built as parity.yml's "Build TLC" step (ant compile dist, JDK 21.0.13), tla2tools.jar sha256 4ff5127be16bf76f204409df2c2a5ada1301d2a350f1a092d5817340744e6a5d. Run with the upstream `tlc` host's JVM flags.
- 4 workers, harness time limit 120 s (the harness kills the process group; the product has no timeout).

## Harness

`harness.ts` is a port of the upstream harness (scripts/test-file.ts, hosts.ts, transcript.ts, conformance.ts at the revision above): same test discovery, expression contexts, arguments, transcript normalization, `correct:` overrides and verdicts. It reads the upstream checkout as data, because this environment does not allow executing the upstream repository's own code. It also keeps stderr, where declines are printed, and the wall time. Validated by running the pinned jar on tlc/cli and tlc/config: 612/614 pass.

    bun harness.ts <tla-ts>/packages/conformance/test <out.jsonl> 120 4 <binary>

`classify.py` makes the compact table: class is match (verdict pass), decline (output carries `prove-it: not native yet:`), noncompletion (time-limit, memory-limit or crash), unrecorded, or wrong (any other mismatch with the recording).

## Results

- `results/baseline.tsv.gz`, `results/candidate.tsv.gz`: one row per run: id, class, verdict, exit, sha256 of the normalized transcript, sha256 of stderr, wall ms, decline reason.
- `results/*.jsonl.gz`: the full raw rows (normalized transcript and stderr); they compress to about 1 MB each.
