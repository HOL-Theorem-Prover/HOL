#!/bin/bash
# Driver: testd/badScript.sml has an unmatched '(' inside its
# Theorem...Proof...QED block.  We check that Holmake exits non-zero
# AND that a "parse error" message reaches the user.  See issue #1993.

set -u

if [ "$#" -lt 1 ]
then
    echo "Usage:"
    echo "  $0 holmake [extra-holmake-args...]" 1>&2
    exit 2
fi

holmake=$1
shift

cd testd

# Force a from-scratch build so that any stale artefacts from a prior
# run can't make Holmake skip the bad-script compile and silently say OK.
"$holmake" "$@" --no_overlay cleanAll 1>/dev/null 2>&1

# --no-cache: don't read or write Holmake's per-script product cache.
# A pre-existing cache hit for this bad script would let Holmake skip
# the script-play entirely, bypassing QUse.hadError and masking the
# very symptom this test exists to detect.
"$holmake" "$@" --no_overlay --no-cache 1>stdout.txt 2>stderr.txt
rc=$?

if [ $rc -eq 0 ]
then
    echo "Holmake unexpectedly succeeded for bad script (rc=0)" 1>&2
    cat stdout.txt 1>&2
    cat stderr.txt 1>&2
    exit 1
fi

# Moscow ML routes the parse error through bin/unquote's stderr; the
# Poly/ML in-process path emits it via the standard `print` (stdout).
# Accept either.
if ! grep -q -E 'parse error' stdout.txt stderr.txt
then
    echo 'FAIL: expected "parse error" message not seen' 1>&2
    cat stdout.txt 1>&2
    cat stderr.txt 1>&2
    exit 1
fi

exit 0
