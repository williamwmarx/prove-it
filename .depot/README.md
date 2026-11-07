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

Tools come from `scripts/ci/bootstrap.sh`, pinned by URL and sha256, not from
setup actions. Only `actions/checkout` is used, pinned to a full SHA.

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
| Depot CI secret | `ONEPASSWORD_PROVE_IT_RELEASE_TOKEN` | That service account's token, scoped to this repository, `main` and `release.yml` |

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
op read --no-newline "op://…" | depot ci secrets set ONEPASSWORD_PROVE_IT_RELEASE_TOKEN --from-stdin --repo williamwmarx/prove-it --branch main --workflow release.yml
```

npm's trusted publishing and provenance work only from CI providers npm
supports (GitHub Actions, GitLab CI/CD, CircleCI). Depot CI isn't one, so
releases use a token instead.
