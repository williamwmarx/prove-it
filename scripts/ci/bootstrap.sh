#!/bin/sh
# Installs CI's exact, checksum-verified tools and prints their bin directories, joined with ":",
# for a step to put first on its PATH:
#
#   PATH="$(scripts/ci/bootstrap.sh bun node):$PATH"
#
# Tools: bun, node (with npm), gitleaks, op (the 1Password CLI), and for the checker benchmark java
# (Temurin JDK), ant (which builds TLC) and rust (rustc, cargo, clippy and rustfmt), which also
# builds the native engine. rust-wasm32 adds the wasm32-unknown-unknown standard library to rust,
# which must come before it, for the engine as WebAssembly. bun-canary is a Bun canary with the ahead-of-time compiler that
# build-binary.ts --aot needs; its bin directory holds a bun, so put it on PATH only for that build.
# Linux x64, which is what depot-ubuntu-24.04 runs, and for bun, node and rust Linux arm64, which
# depot-ubuntu-24.04-arm runs. The x64 bun, node, gitleaks and op pins match Argos's
# scripts/verification/toolchains.json.
set -eu

root=${RUNNER_TEMP:-${TMPDIR:-/tmp}}/prove-it-tools

die() {
  printf 'bootstrap: %s\n' "$1" >&2
  exit 1
}

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64) arch=x64 rust_target=x86_64-unknown-linux-gnu ;;
  Linux-aarch64) arch=arm64 rust_target=aarch64-unknown-linux-gnu ;;
  *) die "only Linux x64 and arm64 are pinned, not $(uname -s) $(uname -m)" ;;
esac
[ $# -gt 0 ] || die "usage: scripts/ci/bootstrap.sh TOOL..."

# name version url sha256 bin-directory-inside-the-archive
pin() {
  case $1-$arch in
    bun-x64) echo "bun 1.4.4 https://registry.npmjs.org/@oven/bun-linux-x64/-/bun-linux-x64-1.4.4.tgz 93ca5a2abe45f3bcac6dd55baff8bb06c4ac824b70f89650b54e5c8b80dbef18 package/bin" ;;
    bun-arm64) echo "bun 1.4.4 https://registry.npmjs.org/@oven/bun-linux-aarch64/-/bun-linux-aarch64-1.4.4.tgz ab95e7e692a53d25a1baa98ee395a17f5f264aedfb3cb15811432d54142f70eb package/bin" ;;
    bun-canary-x64) echo "bun-canary 1.4.4-canary.20261107.1 https://registry.npmjs.org/@oven/bun-linux-x64/-/bun-linux-x64-1.4.4-canary.20261107.1.tgz 16bcf535822d4dadc6c536fa594ff461b3e6df09923ceb63587905d206de8d94 package/bin" ;;
    node-x64) echo "node 24.16.0 https://nodejs.org/dist/v24.16.0/node-v24.16.0-linux-x64.tar.gz 2faf6a387e9b62b888e21c54f01249fb27537ffecf1842f29f4c919d0a59a0ff node-v24.16.0-linux-x64/bin" ;;
    node-arm64) echo "node 24.16.0 https://nodejs.org/dist/v24.16.0/node-v24.16.0-linux-arm64.tar.gz 589f5b6dd4fcfee4dfda73013903c966abaa8abd93dbc9d436544e472b4f0e74 node-v24.16.0-linux-arm64/bin" ;;
    gitleaks-x64) echo "gitleaks 8.30.1 https://github.com/gitleaks/gitleaks/releases/download/v8.30.1/gitleaks_8.30.1_linux_x64.tar.gz 551f6fc83ea457d62a0d98237cbad105af8d557003051f41f3e7ca7b3f2470eb ." ;;
    op-x64) echo "op 2.41.0 https://cache.agilebits.com/dist/1P/op2/pkg/v2.41.0/op_linux_amd64_v2.41.0.zip 498bbaa154f0d90749325a14e04488fcd84930a426ae92ebf421d2a7d793a80a ." ;;
    java-x64) echo "java 21.0.13+9 https://github.com/adoptium/temurin21-binaries/releases/download/jdk-21.0.13%2B9/OpenJDK21U-jdk_x64_linux_hotspot_21.0.13_9.tar.gz d7f5d5cf865a2902b70ff549b97586a7d3f234e016f041ab447ea740c7d66d1c jdk-21.0.13+9/bin" ;;
    ant-*) echo "ant 1.10.15 https://archive.apache.org/dist/ant/binaries/apache-ant-1.10.15-bin.tar.gz 71334d7e5d98cfe53d6c429a648a5021137a967378667306c5f613dff5180506 apache-ant-1.10.15/bin" ;;
    rust-x64) echo "rust 1.99.1 https://static.rust-lang.org/dist/rust-1.99.1-x86_64-unknown-linux-gnu.tar.xz 231fcae47ee950621374725b5fc3b5441d2fbda2955ac45dd7dc816d8876cfe7 toolchain/bin" ;;
    rust-arm64) echo "rust 1.99.1 https://static.rust-lang.org/dist/rust-1.99.1-aarch64-unknown-linux-gnu.tar.xz a48fb1e853be56ce9b8e2751f5464dbd5e16440cd81e237920f3a5e7e806333e toolchain/bin" ;;
    rust-wasm32-*) echo "rust-wasm32 1.99.1 https://static.rust-lang.org/dist/rust-std-1.99.1-wasm32-unknown-unknown.tar.xz 5f628f857dd00a8aa3fcac2e275665d2782066a5795274ed124c5b560f46423c ." ;;
    *) die "no pin for $1 on Linux $arch" ;;
  esac
}

paths=
for tool in "$@"; do
  # shellcheck disable=SC2046
  set -- $(pin "$tool")
  name=$1 version=$2 url=$3 sha256=$4 bin=$5
  directory=$root/$name-$version
  if [ ! -f "$directory/.verified" ]; then
    rm -rf "$directory"
    mkdir -p "$directory"
    archive=$directory/archive
    # GitHub's release downloads return 504 for minutes at a time, so curl retries eight times,
    # waiting twice as long each time, about four minutes in all.
    curl --fail --silent --show-error --location --retry 8 --output "$archive" "$url"
    printf '%s  %s\n' "$sha256" "$archive" | sha256sum --check --quiet - || die "$name $version doesn't match its pinned sha256"
    case $url in
      *.zip) unzip -q "$archive" -d "$directory" ;;
      *.tar.xz) tar -xJf "$archive" -C "$directory" ;;
      *) tar -xzf "$archive" -C "$directory" ;;
    esac
    rm -f "$archive"
    # Rust's standalone archive holds an installer rather than a tree to use in place.
    if [ "$name" = rust ]; then
      "$directory/rust-$version-$rust_target/install.sh" --prefix="$directory/toolchain" --disable-ldconfig \
        --components="rustc,cargo,rust-std-$rust_target,clippy-preview,rustfmt-preview" >/dev/null
      rm -rf "$directory"/rust-*
    fi
    if [ "$name" = rust-wasm32 ]; then
      toolchain=$root/rust-$version/toolchain
      [ -x "$toolchain/bin/rustc" ] || die "rust-wasm32 needs rust $version bootstrapped first"
      "$directory/rust-std-$version-wasm32-unknown-unknown/install.sh" --prefix="$toolchain" --disable-ldconfig >/dev/null
      rm -rf "$directory"/rust-std-*
    fi
    # Bun's npm package ships bun alone; its installer adds bunx, which runs bun as "bun x".
    if [ "$name" = bun ]; then ln -s bun "$directory/$bin/bunx"; fi
    touch "$directory/.verified"
  fi
  paths=${paths:+$paths:}$(CDPATH='' cd -- "$directory/$bin" && pwd -P)
done
printf '%s\n' "$paths"
