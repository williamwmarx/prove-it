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

## startup-effects c2cf44ef (PR 366 final head) vs main 346f96ed

Binary sha256 1b446cc2a5fcb7ab6f2b300b0b54f9c945c74616003d0707486fabf9239dfd4f (main 346f96ed: d4f51420bf2db697e1b0fdc9701ab0991569d2b7319267391622a6cff0fc7d31), each run alone; `results/startup-effects-c2cf44ef.*`, `results/main-346f96ed.*`, report `adjudication/startup-effects-c2cf44ef-vs-main-346f96ed.txt` (and `-vs-main-1446840a.txt`, which differs only by PR 365's four cap_short_circuits_right decline -> match), by `measure.py`.

| class | main 346f96ed | c2cf44ef |
|---|---|---|
| match | 35,107 | 46,888 |
| decline | 36,380 | 24,589 |
| wrong vs the recording | 1,337 | 1,347 |
| noncompletion | 3 | 3 (the same three engine262 time limits) |

Transitions: decline -> match 11,797; decline -> decline 15,615 (reason); decline -> wrong 10, each byte-identical to the pinned jar (`adjudication/pinned-tlc-startup-effects-c2cf44ef.jsonl.gz` for the 6 not run before); match -> decline 16, all `tlc/standard/tlc/{assert_*,print_*_arg_error}` with `a variable assigned a startup definition that failed outside a Java method, which TLC may report as a state it fails to fingerprint`. Subsets: the 6,795: 5,873 match, 922 decline; the 575: 28 match, 537 decline, 10 wrong vs the recording (6 on main too); the 8,671 (`adjudication/startup-effects-8671.txt`): 5,027 match, 3,638 decline, 6 wrong vs the recording.

## startup-effects ea6ac3e7 (one commit over c2cf44ef) vs main 346f96ed

Binary sha256 6bda929fc074121d84e71aaabb3b24cf6d831d397e4f578435671d70282daebb, built in a target directory of its own and run alone; `results/startup-effects-ea6ac3e7.*`, report `adjudication/startup-effects-ea6ac3e7-vs-main-346f96ed.txt`. Classes: match 46,904, decline 24,573, wrong vs the recording 1,347, noncompletion 3 (the same three engine262 time limits). Against main: decline -> match 11,797, decline -> decline 15,615 (reason), decline -> wrong 10 (each byte-identical to the pinned jar), no match lost. Against c2cf44ef: the 16 Assert/Print runs decline -> match, nothing else. Subsets: 6,795 -> 5,873 match; 575 -> 28 match + 10 equal to the jar; 8,671 -> 5,027 match + 6 equal to the jar.

Build check (2026-11-13): my worktrees shared one cargo target directory, whose dep-info paths are relative, so a build could reuse another worktree's crates. Rebuilt in a clean target directory, the binaries measured for main 346f96ed, startup-effects c2cf44ef, wrong-outputs-two b5182e4d and 629cce48, and override reachability d78880bc are byte-identical to the ones measured. The cause-5 candidate binary used as the f6e02eec baseline differs in bytes from a clean f6e02eec build, but the two give identical results on all 72,827 runs (`runs` not kept). Builds since use a target directory per worktree.

## override-user-modules 4e6d8a4c (PR 367: causes 1, 3, 4, 5, reachability, main 32bebcac merged) vs main 32bebcac

Binary sha256 60942fb358f79480a41d30ff8433e63414083469c6a122b8d0bfc95f0187a837, clean target directory, run alone. Main's baseline is the startup-effects ea6ac3e7 run (`git diff ea6ac3e7 32bebcac` is empty). Report `adjudication/override-user-modules-4e6d8a4c-vs-main-32bebcac.txt`. Classes: match 46,952, decline 24,848, wrong vs the recording 1,024, noncompletion 3 (the same three). Transitions: wrong -> match 53, wrong -> decline 270, decline -> decline 10 (reason), match -> decline 5 (reverse_order_chain, the listed by-chance stub comparison), wrong -> wrong 1 (temporal/next_subscript/instance_substituted_expression: wrong on main, now with TLC's 2140 warning but main's error frames, as since cause 4). No new wrong output.

## wrong-outputs-two 3d4050e7 (batch two rebased on main 79c57b9c, narrowed) vs main 79c57b9c

`patches/wrong-outputs-two-79c57b9c/0001-0007`: the six patches of batch two (f6e02eec base) applied cleanly on main 79c57b9c (`results/wrong-outputs-two-ff75f1a6.*`, as rebased), then changed: the lazy-unsizable-sets patch (now 0005) is narrowed, and a membership fix it needs is added before it (0004). Binary sha256 6ec526ef2458d3f6f52f58f74b1b1231c67d07893ac23bcdd51cf3947ba6fec7 (main 79c57b9c: e6984627b21e14c65d3ee9f6c1d7fd9e37a26af986b56982c468fc8561fc7372), clean target directories, run alone. Reports `adjudication/wrong-outputs-two-3d4050e7-vs-main-79c57b9c.txt` and `-vs-ff75f1a6.txt`.

| class | main 79c57b9c | ff75f1a6 (as rebased) | 3d4050e7 |
|---|---:|---:|---:|
| match | 46,956 | 46,995 | 47,062 |
| decline | 24,847 | 24,837 | 24,770 |
| wrong vs the recording | 1,021 | 992 | 992 |
| noncompletion | 3 | 3 | 3 (the same three engine262 time limits) |

Against main: decline -> match 78, wrong -> match 28, wrong -> decline 1, decline -> decline 4 (reason), wrong -> wrong 12 (the cfg integer runs, each byte-identical to the pinned jar), no match lost. Every one of the 106 new matches is byte-identical to the pinned jar (30 from earlier jar runs, 76 in `adjudication/pinned-tlc-wrong-outputs-two-3d4050e7.jsonl.gz`). Against ff75f1a6: 67 decline -> match, nothing else. Parity: conformance --check 769 match, 1 unsupported; native differential at 1 and 4 workers 1,460 of 1,466 print what TLC prints, 6 known, 0 unlisted.

Adversarial specs (`fuzz/gen_lazy.py`, seeds 1-4, 400 each, each run with the pinned jar; `fuzz/lazy-unsized/`): the 129 runs that main matched and ff75f1a6 declined are listed in `the-129.tsv` with their consumer, the decline reason and the result now: all 129 match. On all 1,600 against main: match -> decline 0, decline -> match 158, wrong -> match 66, wrong -> decline 11, wrong -> wrong 5 (byte-identical to main; listed in the patch's fallback.md as known wrong outputs). `two-way-*.txt` give every run's class on main and on each binary.

None of the 129 matched by chance. TLC compares, fingerprints, sizes and enumerates such a set (`SetOfRcdsValue.equals`, `convertAndCache`, `size`, `elements`) through emptiness first, so it answers as the set enumeration main held; `isFinite` is true for every such set that enumerates; a trace's states and a failure's message are printed by the trace evaluator, which keeps the set as TLC does (a state holding `{[a : STRING, b : {}]}` prints so on main and in TLC). Only what the engine writes itself, PrintT and its siblings, `-dump`, a simulation's trace, prints the enumeration where TLC prints the parts (or fails sizing them); those now decline, and only after the run enumerated such a set.

## wrong-outputs-two b8e5a380 (one patch on PR 368 head 8f694a01): operands evaluated before an empty reduction

`patches/wrong-outputs-two-8f694a01/0001-*`. Binary sha256 e742fd199ee4a54ff31f2156c2bf94104340ef623ce5a23bf75afec7f056e644. Review of PR 368 found `Cardinality({} \cap [a : Int, b : {1 \div 0}])` succeeding where TLC and main fail: a reduced `\cap`/`\` evaluated the operand it tests in only through member tests, and IsFiniteSet read `Seq(S)` without evaluating S.

Fuzz (`fuzz/gen_effects.py`, exhaustive, 13,740 cells: a part that fails or prints (`1 \div 0`, `CHOOSE c \in {} : TRUE`, `Assert(FALSE, "a")`, `<<1>>[2]`, `PrintT(5)`, or none) x 10 set shapes holding it x 7 other operands (empty, singletons, Nat, an empty lazy set) x 16 two-operand consumers (`\cap`, `\`, `\cup`, `\subseteq`, `=`, memberships, quantifier, function, IsFiniteSet, UNION, set map, CHOOSE) x left/right, plus 5 one-operand consumers, each under Init, Next or a printed ASSUME). Every cell run on main 79c57b9c, the PR and the fix; the pinned jar on every cell where any two differ (395; `fuzz/effects/three-way.tsv`, `summary-b8e5a380.txt`):

| main -> PR -> fix | cells |
|---|---:|
| match -> wrong -> match | 109 |
| decline -> wrong -> match | 1 |
| decline -> match -> match | 165 |
| decline -> decline -> match | 9 |
| wrong -> match -> match | 76 |
| wrong -> wrong -> match | 19 |
| wrong -> decline -> decline | 3 |
| decline -> decline -> decline | 13 |

Fix: 0 wrong, 0 main match lost. The 1,600 lazy-set specs: unchanged from the PR (0 match -> decline). Suite: no run changed against the PR (`results/wrong-outputs-two-b8e5a380.*`); against main 0 matches lost. Parity: conformance --check 769 match, 1 unsupported; native differential at 1 and 4 workers 1,460/1,466, 6 known, 0 unlisted. Gates: bun 14,631 pass; cargo fmt, clippy -D warnings, cargo test --locked 1,452 pass.
