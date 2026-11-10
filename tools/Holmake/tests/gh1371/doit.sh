#!/bin/bash

# What is being tested is that unquote gets through a malformed
# script: github issue #1371 was a lexer that, while scanning
# declarations, did not handle a Proof line or a Termination token
# and so failed to make progress.  bugScript.sml has a broken Proof
# followed by a sound theorem, and the question is whether the second
# one is still reached.
#
# A loop is unbounded, so any budget comfortably above the real cost
# tells it apart from a healthy run, and the budget should be picked
# for that rather than for tightness.  This wants a few hundredths of
# a second; two seconds looked generous but is close enough to the
# real cost for a loaded machine to exceed it with nothing looping,
# which is what kept happening to the sibling test in gh1353.
ulimit -t 60

unquote=$1

out=$(mktemp "${TMPDIR:-/tmp}/gh1371.XXXXXX") || exit 1
trap 'rm -f "$out"' EXIT

echo "Running unquote"
# Wall alongside CPU: a loop is CPU-bound, so its real time tracks
# its user+sys, while a machine merely too busy shows real time well
# above them.
TIMEFORMAT='unquote: real %3R  user %3U  sys %3S'
time $unquote < bugScript.sml > "$out"

retcode=$?
cat "$out"
echo
echo "unquote completed with code $retcode"

if [ $retcode -ge 128 ]
then
    # Killed by a signal, which here means the CPU limit above: the
    # scan did not terminate.  Which signal arrives is not the same
    # everywhere -- `ulimit -t' sets the soft and hard limits alike,
    # so macOS reports the SIGXCPU at the soft limit (152 = 128+24)
    # while Linux goes straight to the SIGKILL at the hard one
    # (137 = 128+9).
    echo "Killed by signal $(($retcode - 128)): time limit exceeded"
    echo "CPU used (line 1 = this script, line 2 = its children):"
    times
    # Which binary this actually was.  unquote is built by configure
    # and by no Holmakefile rule, so a bin/build can compile the
    # sources and still run an unquote older than them.
    echo "unquote binary under test:"
    ls -l "$unquote"
    exit 1
fi

# A non-zero exit on its own is not a failure: unquote reports the
# parse errors this input carries deliberately, and has returned 1
# for that since well after the test was written.  What matters is
# that it carried on far enough to emit the theorem sitting after the
# broken proof, which is exactly what the lexer bug prevented.
if grep -q '"bar"' "$out"
then
    echo "Reached the declaration after the malformed proof"
    exit 0
else
    echo "FAILED: unquote stopped before the declaration following the"
    echo "malformed proof; its output was expected to mention \"bar\""
    exit 1
fi
