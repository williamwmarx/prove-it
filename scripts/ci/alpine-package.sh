#!/bin/sh
# Builds, tests and packs the native engine's musl platform package for this machine's CPU, on
# Alpine: run it in an Alpine container with the repository at /repo. It installs Bun's musl build
# and Rust's musl toolchain, builds the package with platform-packages.ts, runs the native unit
# tests with the addon, runs install-test, which installs the packed packages with npm and needs
# "native: complete" under Node and Bun, and packs the package into /repo/platform-packages.
set -eu

case "$(uname -m)" in
  x86_64)
    bun_package=@oven/bun-linux-x64-musl
    rustup_target=x86_64-unknown-linux-musl
    rustup_sha256=e6599a1c7be58a2d8eaca66a80e0dc006d87bbcf780a58b7343d6e14c1605cb2
    ;;
  aarch64)
    bun_package=@oven/bun-linux-aarch64-musl
    rustup_target=aarch64-unknown-linux-musl
    rustup_sha256=a97c8f56d7462908695348dd8c71ea6740c138ce303715793a690503a94fc9a9
    ;;
  *)
    echo "alpine-package: no musl package for $(uname -m)" >&2
    exit 1
    ;;
esac

apk add --no-cache bash build-base curl git nodejs npm

tools=$(mktemp -d)
(cd "$tools" && npm pack --silent "$bun_package@1.4.4" && tar -xzf ./*.tgz)
export PATH="$tools/package/bin:$HOME/.cargo/bin:$PATH"

curl --fail --silent --show-error --location --retry 5 --output "$tools/rustup-init" \
  "https://static.rust-lang.org/rustup/archive/1.28.2/$rustup_target/rustup-init"
echo "$rustup_sha256  $tools/rustup-init" | sha256sum -c -
chmod +x "$tools/rustup-init"
# The toolchain comes from native/rust-toolchain.toml, which rustup reads in that directory.
"$tools/rustup-init" -y --quiet --profile minimal --default-toolchain none

git config --global --add safe.directory /repo
cd /repo
bun install --frozen-lockfile --ignore-scripts
cd packages/prove-it
(cd native && rustup toolchain install && cargo test --locked)
bun scripts/platform-packages.ts build
bun run build
addon="$PWD/native/npm/linux-$(node -p process.arch)-musl/prove-it-engine.node"
PROVE_IT_ENGINE_ADDON="$addon" bun test tests/unit/native.test.ts tests/unit/native-search.test.ts \
  tests/unit/engine-store.test.ts tests/unit/engine-fingerprints.test.ts
bun scripts/platform-packages.ts install-test
bun scripts/platform-packages.ts pack /repo/platform-packages
