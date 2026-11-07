#!/bin/sh
# Installs CI's exact, checksum-verified tools and prints their bin directories, joined with ":",
# for a step to put first on its PATH:
#
#   PATH="$(scripts/ci/bootstrap.sh bun node):$PATH"
#
# Tools: bun, node (with npm), gitleaks, op (the 1Password CLI). Linux x64 only, which is what
# depot-ubuntu-24.04 runs. The pins match Argos's scripts/verification/toolchains.json.
set -eu

root=${RUNNER_TEMP:-${TMPDIR:-/tmp}}/prove-it-tools

die() {
  printf 'bootstrap: %s\n' "$1" >&2
  exit 1
}

[ "$(uname -s)-$(uname -m)" = Linux-x86_64 ] || die "only Linux x64 is pinned, not $(uname -s) $(uname -m)"
[ $# -gt 0 ] || die "usage: scripts/ci/bootstrap.sh TOOL..."

# name version url sha256 bin-directory-inside-the-archive
pin() {
  case $1 in
    bun) echo "bun 1.4.4 https://registry.npmjs.org/@oven/bun-linux-x64/-/bun-linux-x64-1.4.4.tgz 93ca5a2abe45f3bcac6dd55baff8bb06c4ac824b70f89650b54e5c8b80dbef18 package/bin" ;;
    node) echo "node 24.16.0 https://nodejs.org/dist/v24.16.0/node-v24.16.0-linux-x64.tar.gz 2faf6a387e9b62b888e21c54f01249fb27537ffecf1842f29f4c919d0a59a0ff node-v24.16.0-linux-x64/bin" ;;
    gitleaks) echo "gitleaks 8.30.1 https://github.com/gitleaks/gitleaks/releases/download/v8.30.1/gitleaks_8.30.1_linux_x64.tar.gz 551f6fc83ea457d62a0d98237cbad105af8d557003051f41f3e7ca7b3f2470eb ." ;;
    op) echo "op 2.41.0 https://cache.agilebits.com/dist/1P/op2/pkg/v2.41.0/op_linux_amd64_v2.41.0.zip 498bbaa154f0d90749325a14e04488fcd84930a426ae92ebf421d2a7d793a80a ." ;;
    *) die "unknown tool: $1" ;;
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
    curl --fail --silent --show-error --location --retry 3 --output "$archive" "$url"
    printf '%s  %s\n' "$sha256" "$archive" | sha256sum --check --quiet - || die "$name $version doesn't match its pinned sha256"
    case $url in
      *.zip) unzip -q "$archive" -d "$directory" ;;
      *) tar -xzf "$archive" -C "$directory" ;;
    esac
    rm "$archive"
    touch "$directory/.verified"
  fi
  paths=${paths:+$paths:}$(CDPATH='' cd -- "$directory/$bin" && pwd -P)
done
printf '%s\n' "$paths"
