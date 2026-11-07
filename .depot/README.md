# CI

Verification runs on Depot CI; the npm release runs on GitHub Actions.

- `.depot/workflows/verification.yml` (Depot CI) builds, typechecks, lints,
  tests and scans the history for credentials on every pull request and push to
  `main`. It holds no credential. Its Gate job reports Verification / Gate, the
  check a `main` ruleset should require. Depot CI registers a workflow when a
  commit that has it reaches `main`, and doesn't run pull requests from forks
  yet.
- `.github/workflows/release.yml` (GitHub Actions) publishes `@atemp/prove-it`
  to npm when a commit on `main` changes the version in
  `packages/prove-it/package.json`, then tags the commit `v<version>`. A
  version npm already has publishes nothing, so running it by hand retries a
  failed release.

The release is on GitHub Actions because npm's trusted publishing accepts only
GitHub-hosted runners (or GitLab.com and CircleCI cloud). Depot CI's OIDC
tokens come from Depot's own issuer, which npm doesn't accept. With trusted
publishing, npm trusts `release.yml` in this repository by name, no npm token
exists, and npm attaches a provenance statement to each version.

Tools come from `scripts/ci/bootstrap.sh`, pinned by URL and sha256, not from
setup actions. Only `actions/checkout` is used, pinned to a full SHA.

## Releasing

Bump `version` in `packages/prove-it/package.json` in a pull request and
merge it. npm versions are permanent: one that is published can't be reused,
and can be unpublished only within 72 hours.

## Setup

The first version is published with a token, because npm sets trusted
publishing on a package's own settings page:

1. On npmjs.com, generate a granular access token: read and write on all
   packages, bypassing two-factor authentication, expiring in a day.
2. Add it as the repository's Actions secret `NPM_TOKEN`.
3. Run Release by hand on `main`.
4. On the package's npm page, go to Settings, Trusted publishing, and add
   GitHub Actions: user `williamwmarx`, repository `prove-it`, workflow
   `release.yml`, environment `npm`. Allow `npm publish`.
5. Delete the `NPM_TOKEN` secret and revoke the token. Then, under the same
   settings, require two-factor authentication and disallow tokens, so the
   workflow is the only way to publish.
