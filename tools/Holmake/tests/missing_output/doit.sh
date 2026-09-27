#!/bin/bash
# Driver: testd/Holmakefile has one rule whose command exits 0 without
# creating its target, alongside three that must not be mistaken for it
# -- a phony target, a multi-command rule whose earlier commands create
# nothing, and a command whose errors are ignored.
#
# Without --strict-outputs the liar draws a warning and the build still
# succeeds; with it, the build fails.  Each case runs under -j1, which
# uses HM_GraphBuildJ1, and under the default job count, which on Poly
# uses multibuild; the two must reach the same verdict.

set -u

if [ "$#" -lt 1 ]
then
    echo "Usage:" 1>&2
    echo "  $0 holmake [extra-holmake-args...]" 1>&2
    exit 2
fi

holmake=$1
shift
# The caller's extra flags (--holstate=... under Poly).  Held in a
# variable because run_case's own "$@" shadows the script's.
hmopts=("$@")

cd testd

# label, expected-exit-status ("ok"/"fail"), extra flags
run_case() {
    label=$1 expect=$2
    shift 2

    /bin/rm -f multi
    "$holmake" "${hmopts[@]}" "$@" --no_overlay >stdout.txt 2>stderr.txt
    rc=$?

    if [ "$expect" = ok ] && [ $rc -ne 0 ] ; then
        echo "FAIL ($label): Holmake failed when it should not have" 1>&2
        cat stdout.txt stderr.txt 1>&2
        exit 1
    fi
    if [ "$expect" = fail ] && [ $rc -eq 0 ] ; then
        echo "FAIL ($label): Holmake succeeded despite an uncreated target" 1>&2
        cat stdout.txt stderr.txt 1>&2
        exit 1
    fi

    if ! grep -q "did not create.*liar" stdout.txt stderr.txt ; then
        echo "FAIL ($label): liar was not reported" 1>&2
        cat stdout.txt stderr.txt 1>&2
        exit 1
    fi

    # none of these promises a file, so none may be reported
    for t in phony_ok multi ignored ; do
        if grep -q "did not create.*\b$t\b" stdout.txt stderr.txt ; then
            echo "FAIL ($label): $t was wrongly reported as missing" 1>&2
            cat stdout.txt stderr.txt 1>&2
            exit 1
        fi
    done
}

run_case "warn/-j1"     ok   -j1
run_case "warn/-jN"     ok
run_case "strict/-j1"   fail -j1 --strict-outputs
run_case "strict/-jN"   fail --strict-outputs

exit 0
