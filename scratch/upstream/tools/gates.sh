#!/bin/bash
# gates.sh <worktree> <target-dir>: AGENTS.md's checks, with this container's JVM variables unset.
set -u; W=$1; T=$2; unset JAVA_TOOL_OPTIONS _JAVA_OPTIONS; export PATH="/root/.bun/bin:$PATH"
cd $W && bun install --frozen-lockfile --ignore-scripts >/dev/null 2>&1
for c in typecheck lint format:check test; do bun run $c > $T.bun-$c.log 2>&1; echo "bun $c: $?"; done
cd $W/packages/prove-it/native
cargo fmt --check > $T.fmt.log 2>&1; echo "cargo fmt: $?"
CARGO_TARGET_DIR=$T cargo clippy --locked --all-targets -- -D warnings > $T.clippy.log 2>&1; echo "clippy: $?"
CARGO_TARGET_DIR=$T cargo test --locked > $T.test.log 2>&1; echo "cargo test: $?"
grep -E "^test result" $T.test.log | awk '{p+=$4; f+=$6} END {print "passed", p, "failed", f}'
