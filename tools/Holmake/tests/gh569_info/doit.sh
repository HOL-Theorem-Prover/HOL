#!/bin/bash
# Driver for gh569_info.  Runs Holmake in testd/, captures stdout and stderr
# separately, then checks for expected substrings.  The HOL Holmakefile is
# read more than once (for INCLUDES discovery and again to build), so we
# check for presence/absence rather than insisting on an exact line count.

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

if [ $rc -ne 0 ]
then
    echo "Holmake failed (exit $rc)"
    cat stderr.txt 1>&2
    exit 1
fi

check_present () {
    local stream=$1 pattern=$2 file=$3
    if ! grep -q -E "$pattern" "$file" ; then
        echo "FAIL ($stream): expected /$pattern/ not seen in $file" 1>&2
        exit 1
    fi
}

check_absent () {
    local stream=$1 pattern=$2 file=$3
    if grep -q -E "$pattern" "$file" ; then
        echo "FAIL ($stream): unexpected /$pattern/ in $file" 1>&2
        exit 1
    fi
}

check_present stdout '^top-level-info$'       stdout.txt
check_present stdout '^chosen-branch$'        stdout.txt
check_present stdout '^one,two,three$'        stdout.txt

check_absent  stdout 'DO-NOT-FIRE'            stdout.txt
check_absent  stdout 'wrong-branch'           stdout.txt

check_present stderr '/Holmakefile:[0-9]+: top-level-warning$' stderr.txt
check_absent  stderr 'DO-NOT-FIRE'            stderr.txt

exit 0
