#!/bin/bash
# Driver: testd/badLib.sml has a missing closing `}` in a record
# literal.  HOLSourceParser recovers silently by synthesising the
# `}` when it emits to PolyML, so the recovered SML compiles and the
# old fix (5827ee0f0f) only detected the error at the very end of
# `bin/hol run` -- after mainScript.sml's export_theory had already
# run and written mainTheory.dat.  We want Holmake to exit non-zero
# AND for mainTheory.dat to be absent (proof that export_theory was
# prevented).

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
# run can't make Holmake skip the bad-library compile and silently
# say OK.
"$holmake" "$@" --no_overlay cleanAll 1>/dev/null 2>&1

# --no-cache: as in tests/gh1993, don't read or write Holmake's
# per-script product cache; a pre-existing cache hit would let
# Holmake skip the script-play and mask the failure mode.
"$holmake" "$@" --no_overlay --no-cache 1>stdout.txt 2>stderr.txt
rc=$?

if [ $rc -eq 0 ]
then
    echo "Holmake unexpectedly succeeded for bad library (rc=0)" 1>&2
    cat stdout.txt 1>&2
    cat stderr.txt 1>&2
    exit 1
fi

if ! grep -q -E 'parse error' stdout.txt stderr.txt
then
    echo 'FAIL: expected "parse error" message not seen' 1>&2
    cat stdout.txt 1>&2
    cat stderr.txt 1>&2
    exit 1
fi

# The dependent script's export_theory must NOT have run.
if [ -f mainTheory.dat ]
then
    echo 'FAIL: mainTheory.dat exists; export_theory should have been prevented' 1>&2
    ls -l mainTheory.* 1>&2
    exit 1
fi

exit 0
