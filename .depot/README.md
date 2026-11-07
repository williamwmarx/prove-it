# Depot CI

Every CI workflow runs on Depot CI. GitHub Actions runs none.

- `workflows/verification.yml` builds, typechecks, lints, tests and scans the
  history for credentials on every pull request and push to `main`. It holds no
  credential. Its Gate job reports Verification / Gate, the check a `main`
  ruleset should require. Depot CI doesn't run pull requests from forks yet.
- `workflows/release.yml` publishes `@atemp/prove-it` to npm when a commit on
  `main` changes the version in `packages/prove-it/package.json`, then tags the
  commit `v<version>`. A version npm already has publishes nothing, so running
  it by hand retries a failed release.
- `workflows/benchmark.yml` times Prove It against other TLA+ model checkers,
  by hand or weekly, never on a pull request ("Benchmark" below).

Tools come from `scripts/ci/bootstrap.sh`, pinned by URL and sha256, not from
setup actions. Only `actions/checkout` and `actions/upload-artifact` are used,
pinned to full SHAs.

## Releasing

Bump `version` in `packages/prove-it/package.json` in a pull request and
merge it. The first version, already in `package.json`, is released by running
the workflow by hand:

```bash
depot ci run --forge github --repo williamwmarx/prove-it --workflow .depot/workflows/release.yml --follow
```

npm versions are permanent: one that is published can't be reused, and can
be unpublished only within 72 hours.

## Credentials

One credential: the npm token that publishes.

| Where | Name | Holds |
| --- | --- | --- |
| 1Password Environment `prove-it-release` | `NPM_TOKEN` | npm granular access token, read and write; on all packages until the first publish, then `@atemp/prove-it` only |
| 1Password service account `prove-it-release` | | Read access to that Environment alone |
| Depot CI secret | `ONEPASSWORD_PROVE_IT_RELEASE_TOKEN` | That service account's token, scoped to this repository, `main`, `release.yml` and the `npm` environment |

The Environment's ID is `ONEPASSWORD_ENVIRONMENT_ID` in `release.yml`.

Only the publish step holds the service account token, and it runs no package
code: it publishes the tarball an earlier step packed, with `--ignore-scripts`.
The tests and build run earlier in the same job, so install runs with
`--ignore-scripts` too, and every dependency change should be reviewed.

npm limits a write token to 90 days. To rotate it:

1. On npmjs.com, generate a new granular token with the same scope.
2. Replace `NPM_TOKEN` in the `prove-it-release` Environment.
3. Revoke the old token.

To rotate the service account token, rotate it in 1Password under Developer,
Service accounts, then set it again:

```bash
op read --no-newline "op://…" | depot ci secrets set ONEPASSWORD_PROVE_IT_RELEASE_TOKEN --from-stdin --repo williamwmarx/prove-it --branch main --workflow release.yml --env npm
```

npm's trusted publishing and provenance work only from CI providers npm
supports (GitHub Actions, GitLab CI/CD, CircleCI). Depot CI isn't one, so
releases use a token instead.

## Benchmark

`workflows/benchmark.yml` runs `packages/prove-it/scripts/bench-suite.ts` on
one `depot-ubuntu-24.04-4` machine (4 CPUs, 16 GB): the three specs in
`packages/prove-it/benchmarks/` and fifteen models from the pinned corpora, 1
thousand to 724 thousand distinct states, listed in `bench-suite.json`. The
checkers:

| Checker | What runs | Pinned by |
| --- | --- | --- |
| `tlc`, `tlc-auto` | TLC 1.8.0 on Temurin JDK 21, one worker and one per core | `TLC_COMMIT` in the workflow; Ant and the JDK in `bootstrap.sh` |
| `tla-ts` | tla-ts 0.0.8 under Node | `scripts/ci/tla-ts/package-lock.json` |
| `tla-rs` | tla-rs 0.24.11 (crate `tla-checker`), built with Rust 1.99.1 | the workflow's `cargo install --locked`; Rust in `bootstrap.sh` |
| `prove-it` | Prove It's compiled binary, from the commit the run checks out | |
| `prove-it-aot` | Prove It compiled to machine code by Bun's ahead-of-time compiler (`build-binary.ts --aot`), which runs actions as closures since it interprets code made with `new Function` | the Bun canary in `bootstrap.sh` (`bun-canary`) |
| `prove-it-node` | `dist/cli.js` under Node, as an npm user runs it | |
| `prove-it-bun` | `dist/cli.js` under Bun, off by default | |

TLC 1.8.0 is a pre-release whose jar is rebuilt nightly, so it can't be pinned
by checksum. The workflow builds it with Ant from the `tlaplus/tlaplus` commit
in `TLC_COMMIT` instead. TLC 1.7.4, the last fixed release, starts slower and
can't read the `ALIAS` in TokenRing's config.

Each round runs every checker once on a model before the next round, and every
run is a fresh process, so wall time includes startup. The table gives the
median wall time with the CPU time and the fastest and slowest run. A checker's
verdict, distinct states, depth (except TLC on every core, whose workers can
report a deeper level than its search reached) and generated states (except
tla-rs, which counts transitions) must match TLC's on one worker; one that disagrees, fails or
times out says so in its cell, takes no more runs on that model and is left out
of the speedups. The run fails only when Prove It fails or disagrees, or when
TLC fails on a model with no recorded TLC result (`expected.json`) to check
against.

Run it by hand from the Depot dashboard or with
`depot ci dispatch --repo williamwmarx/prove-it --workflow benchmark.yml --ref main`
and its inputs as repeated `--input key=value`: `runs`, `filter`, `checkers`
and `timeout`. The run's summary has the
table, and its artifact the JSON with every run. A full run takes about half
an hour.

To bump a checker, change its pin (`TLC_COMMIT`, the lockfile, the crate
version, or a URL and sha256 in `bootstrap.sh`) and run the benchmark once by
hand. Other
TLA+ tools were left out: Apalache and Quint check symbolically or a different
language, PlusPy and Spectacle explore behaviors without a command-line model
checker that reports TLC's counts, and the remaining Rust, Go and C checkers on
GitHub have a handful of stars.
