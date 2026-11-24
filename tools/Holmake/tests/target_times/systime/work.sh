#!/bin/sh
# work.sh N
#
# Spend CPU that lands almost entirely in *system* time -- `bs=1' makes
# dd issue a read and a write syscall per byte -- and then report what
# this recipe actually cost, so the test can compare Holmake's figure
# against the shell's own.  Neither number is a wall clock, so the
# comparison says the same thing on any machine.  Measured here at
# roughly three parts system to one part user: counting only `cutime'
# records this recipe at about a quarter of what it cost.
#
# `times' prints this shell's own user and system time on its first
# line and its waited-for children's on the second, each as
# <min>m<sec>s.  All four summed is the recipe's cost so far -- the
# same quantity the kernel hands Holmake when it reaps the shell.
#
# It must be *redirected*, never piped: every element of a pipeline
# runs in a subshell, and a subshell has reaped no children, so
# `times | ...' reports zeroes.  The sed and awk below therefore run
# after the measurement and are not in it, which leaves self-measured
# a little under what Holmake sees.  The test allows for that.

dd if=/dev/zero of=/dev/null bs=1 count="$1" 2>/dev/null
times > raw-times
sed 's/[ms]/ /g' raw-times |
  awk '{for (i = 1; i <= NF; i += 2) t += $i * 60 + $(i+1)}
       END {printf "%.3f\n", t}' > self-measured
