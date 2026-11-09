#!/bin/bash

cd testd
ulimit -t 2
if [ "$#" -ne 2 ]
then
    echo "Usage:"
    echo "  $0 holstatefile holmake"
    exit 1
fi

holstate=$1
holmake=$2

echo "Running Holmake in testd directory"
$holmake --holstate=$holstate

retcode=$?
echo "Holmake completed with code $retcode"

if [ $retcode -eq 0 ]
then
    exit 1
elif [ $retcode -ge 128 ]
then
    # Killed by a signal, which here means the CPU limit set above:
    # Holmake looped instead of stopping at the parse error.  Which
    # signal arrives is not the same everywhere -- `ulimit -t' sets
    # the soft and hard limits alike, so macOS reports the SIGXCPU at
    # the soft limit (152 = 128+24) while Linux goes straight to the
    # SIGKILL at the hard one (137 = 128+9).  Testing for 152 alone,
    # as this did, let a looping Holmake through on Linux entirely.
    echo "Killed by signal $(($retcode - 128)): time limit exceeded"
    # Holmake wants about a tenth of a second here on an idle machine
    # and a third under load, so a trip is a long way from anything
    # measured, and the number is worth having rather than guessing
    # at.  `times' prints this shell's own user/sys first and its
    # children's -- essentially all Holmake's -- second.
    echo "CPU used (line 1 = this script, line 2 = its children):"
    times
    exit 1
else
    exit 0
fi
