#!/bin/bash
# Driver: testd/Holmakefile invokes $(error stop now); we check that
# Holmake exits non-zero and emits the GNU-make-style abort line.

set -u

if [ "$#" -ne 2 ]
then
    echo "Usage:"
    echo "  $0 holstate holmake" 1>&2
    exit 2
fi

holstate=$1
holmake=$2

cd testd

"$holmake" --holstate="$holstate" --no_overlay \
    1>stdout.txt 2>stderr.txt
rc=$?

if [ $rc -eq 0 ]
then
    echo "Holmake unexpectedly succeeded (rc=0)" 1>&2
    cat stderr.txt 1>&2
    exit 1
fi

if ! grep -q -E '/Holmakefile:[0-9]+: \*\*\* stop now\.  Stop\.$' \
                stderr.txt ; then
    echo "FAIL: expected $(error ...) message not seen in stderr:" 1>&2
    cat stderr.txt 1>&2
    exit 1
fi

exit 0
