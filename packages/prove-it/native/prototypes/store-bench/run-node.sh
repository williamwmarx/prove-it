#!/bin/sh
# Bundles the workload with Bun and runs it under Node, as scripts/run.ts does.
cd "$(dirname "$0")" && bun build workload.ts --target node --outfile workload.node.mjs >/dev/null && node workload.node.mjs "$@"
