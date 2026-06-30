#!/usr/bin/env bash
# Backwards-compatible entry point for the TacticToe selftests.
set -euo pipefail

HERE="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
exec "$HERE/src/tactictoe/run-selftests.sh" "$@"
