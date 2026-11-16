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
started=$SECONDS
time $unquote < bugScript.sml > "$out"

retcode=$?
elapsed=$(($SECONDS - $started))
cat "$out"
echo
echo "unquote completed with code $retcode after ${elapsed}s"

# The exit code decides nothing here, because it cannot: a shell
# reports a signalled death as 128 plus the signal, and an exit code
# of 255 is equally something a program may return by itself.  The
# Moscow ML unquote does exactly that for the parse errors this
# input carries on purpose, where the Poly/ML one returns 1, and
# reading either as "killed" was wrong.
#
# What the test is about needs none of that.  Issue #1371 was a lexer
# that never got past the malformed proof, so the question is whether
# the declaration after it came out, and a scan that failed to
# terminate cannot have got there however it was eventually stopped.
if grep -q '"bar"' "$out"
then
    echo "Reached the declaration after the malformed proof"
    exit 0
fi

echo "FAILED: unquote stopped before the declaration following the"
echo "malformed proof; its output was expected to mention \"bar\""
# Say which way it stopped.  Running out the clock set above is the
# non-termination this test exists for; stopping early is some other
# fault, and the two want different attention.
if [ $elapsed -ge 55 ]
then
    echo "It ran for ${elapsed}s against the limit set above, so the"
    echo "scan did not terminate."
    echo "CPU used (line 1 = this script, line 2 = its children):"
    times
fi
# Which binary this actually was.  unquote is built by configure and
# by no Holmakefile rule, so a bin/build can compile the sources and
# still run an unquote older than them.
echo "unquote binary under test:"
ls -l "$unquote"
exit 1
