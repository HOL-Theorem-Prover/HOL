#!/usr/bin/env bash
# Run only the TacticToe selftests.  This assumes HOL and the TacticToe
# dependencies have already been built.
set -euo pipefail

HERE="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
HOLDIR="$(CDPATH= cd -- "$HERE/../.." && pwd)"
cd "$HOLDIR"

export HOLSELFTESTLEVEL="${HOLSELFTESTLEVEL:-1}"

echo "Running TacticToe selftests only..."
rm -f src/tactictoe/src/tactictoe-selftest.log
rm -f src/tactictoe/selftest/tactictoe2-selftest.log

bin/Holmake -C src/tactictoe/src tactictoe-selftest.log
bin/Holmake -C src/tactictoe/selftest tactictoe2-selftest.log

echo "TacticToe selftests passed."
echo "Logs:"
echo "  src/tactictoe/src/tactictoe-selftest.log"
echo "  src/tactictoe/selftest/tactictoe2-selftest.log"
