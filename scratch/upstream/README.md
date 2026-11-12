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

## Findings (startup-guards ef8d0a55 vs main cb48b6eb)

| class | baseline | candidate |
| --- | ---: | ---: |
| match | 35,101 | 40,712 |
| decline | 36,363 | 30,749 |
| wrong vs the recording | 1,360 | 1,363 |
| noncompletion (120 s limit: tlc/engine262/{functions_and_arrays,print_sum,uncaught_type_error}) | 3 | 3 |

Transitions: decline->match 5,723; match->decline 112; decline->wrong-vs-recording 4; wrong->decline 1 (operators/bag_minus/bag_minus_union#assume); decline->decline 30,636 (4,614 of them with a changed reason); match->match 34,989; wrong->wrong 1,359 (byte-identical); noncompletion 3. 10,454 runs changed class or output. No run crashed.

Pinned-jar adjudication (`adjudication/`, 7,652 runs of tla2tools.jar d8fb231d):

- New wrong outputs: none. Every changed run where the candidate is not a match is a decline (4,727) or equals the pinned jar (the 4 decline->wrong-vs-recording runs, a SANY precedence version gap; see `adjudication/changed-not-match-wrong-vs-recording.md`).
- decline->match sample of 300 (seed 20261112): all 300 equal the pinned jar.
- guard-overreach (6,795): 5,723 match, 1,072 still decline, 0 wrong (baseline: all 6,795 decline).
- startup-wrong-cases (575): 566 decline, 0 match, 9 match the pinned jar only (recording differs), 0 wrong (baseline: 569 decline, 6 pinned-jar-only).
- Regressions: 112 baseline matches now decline, all `#assume` runs, all with reason `an assumption that fails to evaluate: evaluating the assumption again: a startup definition that failed where TLC may fail otherwise: ...`; on all 112 the baseline output also equals the pinned jar. List in `adjudication/regressions.tsv`.
- Pre-existing, unchanged by the branch: 553 runs differ from the pinned jar on both binaries with byte-identical output (236 exit differs, 317 text only; 296 under tlc/standard). Listed in `adjudication/report.json`.
- `hang_postcond` is not in the upstream suite.

## Winning back the 112: local startup-guards fa0b6e54 (ef8d0a55 + c25fc64b + fa0b6e54)

Binary sha256 37ba9c90f3f01590ecfebede746e34caf0dfe0e06fd2fc6479b698076d6d7486. Full run of 72,827 against the baseline (`results/startup-guards-fa0b6e54.*`), adjudicated with the same pinned-jar runs (no new run needed: every non-match change is a decline or was already adjudicated).

| class | main cb48b6eb | ef8d0a55 | fa0b6e54 |
| --- | ---: | ---: | ---: |
| match | 35,101 | 40,712 | 41,124 |
| decline | 36,363 | 30,749 | 30,336 |
| wrong vs the recording | 1,360 | 1,363 | 1,364 |
| noncompletion | 3 | 3 | 3 |

- The 112: all match. Baseline matches lost: 0. ef8d0a55 matches lost: 0.
- guard-overreach (6,795): 5,981 match, 814 decline, 0 wrong.
- startup-wrong-cases (575): 537 decline, 28 match, 10 match the pinned jar only, 0 wrong.
- New wrong outputs vs the pinned jar: none. Wrong vs the recording beyond the jar: the same 553 runs as main, byte-identical; the other 811 equal the jar (version gap), 4 of them the precedence cases.
- Found on the way: ef8d0a55 gives a wrong output not in the upstream suite, `{DOMAIN [b \in SUBSET {1} |-> 1] \ (3 .. 3), CHOOSE y \in {} : TRUE}` in a failing startup definition (TLC: the CHOOSE failure; ef8d0a55: a mistyped membership in 3..3). c25fc64b declines it (fixture `definition-fails-lazy-domain`).
- `adjudication/pre-existing-553.txt`: the 553 grouped by first differing line.

## New baseline: main 1446840a (PR 362) vs main cb48b6eb

Binary sha256 2ba048fa086008ad1413aab3c03ed3f673453a3a46a07c3179860b3a20db3dda, `results/main-1446840a.*`; pinned-jar runs of every run whose class changed in `adjudication/pinned-tlc-main-1446840a.jsonl.gz`.

| class | cb48b6eb | 1446840a |
| --- | ---: | ---: |
| match | 35,101 | 35,103 |
| decline | 36,363 | 36,384 |
| wrong vs the recording | 1,360 | 1,337 |
| noncompletion | 3 | 3 |

131 runs changed output; 36 changed class. No wrong output changed and none is new: the 530 runs that differ from the jar are byte-identical to cb48b6eb's (18 of cb48b6eb's 553 now decline, 5 now match).

- wrong -> decline 18, each wrong against the jar before: tlc/errors/TLC_WRONG_RECORD_FIELD_NAME/unknown_string_field_keeps_record, tlc/errors/TLC_WRONG_TUPLE_FIELD_NAME/out_of_range_index_keeps_tuple, expressions/except/missing_{field,function_key,intermediate,nested,tuple_index}_warns#assume, missing_then_valid_clause#assume, conditional/if_returning_set_is_lazy_in_application#assume, functions/lazy/{apply_keeps_constructor_lazy,defined_function_kept_lazy,domain_of_cartesian_function_skips_body,domain_of_subset_function_skips_body,nested_apply_stays_lazy,parameter_function_kept_lazy}#assume, functions/recursive/compare_forces_every_branch#{init,next}, let/let_function_kept_lazy_when_applied#assume.
- wrong -> match 5 (sets/binary/cup_nat_integer_reaches_string, all contexts) and decline -> match 5 (sets/binary/cup_nat_swaps_reducible_first, all contexts), each equal to the jar.
- Regressions, match -> decline 8, each equal to the jar on cb48b6eb: sets/binary/cap_short_circuits_right#{init,next,invariant,property} ("the engine stopped: enumerated Nat"); except/reducible_function_forced_before_except#assume, functions/lazy/apply_reaches_erroring_body#assume, functions/recursive/compare_forces_every_branch#assume ("the body of a function TLC keeps lazy, at a key it may not evaluate"); imported/tlc/tool/ValueSemanticsAssumeTest/ValueSemanticsAssume ("an EXCEPT of a key the function lacks, which TLC warns of").

## override-user-modules 1e58e538 (over main 1446840a): cause 1 of the 553

Binary sha256 1ef165e1b98e05f30301bb8db2c414544747bf60ce2f4b6789befbf5b613cb93; `patches/override-user-modules/`; `results/override-user-modules-1e58e538.*`. Against main 1446840a: 274 runs changed: wrong -> decline 264 (each differed from the pinned jar: transitive_closure 155, randomization 95, any_set 10, TLC_MODULE_TRANSITIVE_CLOSURE 4), decline -> decline 5 (reason), match -> decline 5 (tlc/standard/transitive_closure/reverse_order_chain, all contexts, which compared two stub values; listed in fallback.md). No run prints a stub body any more. No new wrong output. Classes: match 35,098, decline 36,653, wrong vs the recording 1,073, noncompletion 3.

## override-user-modules a94fcb14: cause 3 (FingerprintException vs nested expressions)

Binary sha256 ec2b13ed8d384a882119c65617e7e449f74c0255f5d2ecd3c04806ddc691e6b9; `patches/override-user-modules/0002-*`; `results/override-user-modules-a94fcb14.*`. Against 1e58e538: 29 runs changed, all wrong -> match (the 25 space_membership__*__invariant_non_boolean, Github715-independent; tlc/expressions/sets/function_set/enumerate_nat_domain in 4 contexts). Nothing else changed. Classes: match 35,127, decline 36,653, wrong vs the recording 1,044, noncompletion 3. Of cause 3's 37 runs, the remaining 8 are other causes: sets/enum/too_many_elements (TLC's 1,000,000-element limit, 4), Github715 (a config operator as the spec), temporal/levels/config_operator_{action,temporal}_in_invariant (a level check), and sets/union/combine_compares_mixed_eagerly#next, which the eager UNION of startup-guards fa0b6e54 addresses once merged.

## override-user-modules 02f7849c: cause 4 (next-state subscript warnings 2139/2140)

Binary sha256 0372d4d82d95fe3f6a78d854dd998198197a9f1ff1ee8dd4699524d1ca457841; `patches/override-user-modules/0003-*`; `results/override-user-modules-02f7849c.*`. Against a94fcb14: 26 runs changed, all cause 4: wrong -> match 24, wrong -> decline 1 (temporal/next_subscript/definition_overridden_in_config, a subscript the configuration substitutes), wrong -> wrong 1 (temporal/next_subscript/instance_substituted_expression, whose subscript warning now matches but whose error stack frames differ, another cause). Nothing else changed. Classes: match 35,151, decline 36,654, wrong vs the recording 1,019, noncompletion 3.

## override-user-modules 9b51e6ea (over origin/override-user-modules b929e751): cause 5 (2144 EXCEPT warning)

b929e751 (the coordinator's branch: causes 1, 3 and 4 over main 2af9b885) measured first, `results/override-user-modules-b929e751.jsonl.gz`: against 02f7849c, 4 decline -> match from main, nothing else of note. Then cause 5, binary sha256 bff221bf30ffac59fc62c5b80f34eb205346403079cf29380d4c34f2a4193d13, `patches/override-user-modules-cause5/`, `results/override-user-modules-9b51e6ea.*`: against b929e751, 10 runs changed: wrong -> decline 5 (tlc/expressions/except/missing_lazy_key_warns, all contexts), decline -> decline 5 (reason). Classes: match 35,155, decline 36,655, wrong vs the recording 1,014, noncompletion 3.

## PR 367 review findings: override-user-modules 0004, 0005 (over b929e751)

`patches/override-user-modules/0004-*`, `0005-*`; cause 5 is withdrawn (its patch stays under `patches/override-user-modules-cause5/`, not for the PR). Full suite of c99d69de against b929e751: no run changed. Differential (`fuzz/`): `gen_fuzz.py` seeds 7 (160 subscripts) and 8 (200 subscripts) plus 84 override shapes, each run with the pinned jar, main 346f96ed and the branch: branch wrong 0; main matches the jar and the branch declines 0; subscripts wrong on main and matching on the branch 236; override shapes wrong on main and declined on the branch 12.
