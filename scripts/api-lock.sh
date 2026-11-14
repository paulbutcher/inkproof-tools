#!/usr/bin/env bash
# Prints the public API of the given root modules (default: this library's), one line per declaration; CI compares it with API.lock.
# Regenerate with: scripts/api-lock.sh <root module>... > API.lock
set -euo pipefail
cd "$(dirname "$0")/.."
lake build >&2
if [ $# -eq 0 ]; then set -- InkproofTools.ApiLock InkproofTools.AxiomCheck InkproofTools.Test.Driver InkproofTools.Test.Harness InkproofTools.Test.Platform; fi
lake exe api-lock "$@"
