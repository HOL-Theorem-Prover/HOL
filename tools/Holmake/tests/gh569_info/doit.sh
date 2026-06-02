#!/bin/bash
# Driver for gh569_info.  Runs Holmake in testd/, captures stdout and stderr
# separately, then asserts each $(info)/$(warning) message fires exactly
# once -- locks in the single-fire semantics after the preexec-pass parse
# of Holmakefiles was silenced.  A second invocation with -q checks that
# quiet mode suppresses $(info)/$(warning) entirely.

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

"$holmake" "$@" --no_overlay 1>stdout.txt 2>stderr.txt
rc=$?

if [ $rc -ne 0 ]
then
    echo "Holmake failed (exit $rc)"
    cat stderr.txt 1>&2
    exit 1
fi

check_count () {
    local stream=$1 pattern=$2 expected=$3 file=$4
    local got
    got=$(grep -c -E "$pattern" "$file" || true)
    if [ "$got" != "$expected" ] ; then
        echo "FAIL ($stream): expected $expected matches of /$pattern/ in $file, got $got" 1>&2
        cat "$file" 1>&2
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

# Patterns are not anchored at start: under mosml, output_functions
# prepends "Holmake: " to info/warn messages (since mosml is single-job
# and usepfx is true).  The message tails are distinctive enough.
check_count  stdout 'top-level-info$'        1 stdout.txt
check_count  stdout 'chosen-branch$'         1 stdout.txt
check_count  stdout 'one,two,three$'         1 stdout.txt

check_absent stdout 'DO-NOT-FIRE'              stdout.txt
check_absent stdout 'wrong-branch'             stdout.txt

check_count  stderr '/Holmakefile:[0-9]+: top-level-warning$' 1 stderr.txt
check_absent stderr 'DO-NOT-FIRE'              stderr.txt

# Quiet mode: -q maps to chattiness 0 in Holmake, which makes the
# output_functions info/warn channels into no-ops.  Since $(info) and
# $(warning) now route through those channels, they should produce no
# output.
"$holmake" "$@" --no_overlay -q 1>stdout.txt 2>stderr.txt
rc=$?

if [ $rc -ne 0 ]
then
    echo "Holmake -q failed (exit $rc)"
    cat stderr.txt 1>&2
    exit 1
fi

check_absent stdout 'top-level-info'           stdout.txt
check_absent stdout 'chosen-branch'            stdout.txt
check_absent stdout 'one,two,three'            stdout.txt
check_absent stdout 'DO-NOT-FIRE'              stdout.txt
check_absent stderr 'top-level-warning'        stderr.txt
check_absent stderr 'DO-NOT-FIRE'              stderr.txt

exit 0
