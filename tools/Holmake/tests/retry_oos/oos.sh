#!/bin/sh
# oos.sh NFAILS MODE
#
# A recipe that fails its first NFAILS invocations and succeeds after
# that, counting invocations in ./.oos.count so the test can see how
# many attempts Holmake made.  The counter is per-directory, so each
# test subdirectory gets its own.
#
# MODE picks what a failing invocation writes to stderr:
#
#   oos    the message Poly/ML's runtime prints when it cannot grow the
#          ML heap -- the thing --retry-oos looks for.  The wording is
#          copied verbatim from libpolyml/processes.cpp, where it has
#          been unchanged since 2007; multibuild's oos_markers must
#          agree with it.
#   plain  an ordinary error message, which must NOT provoke a retry.
#
# There is no locking: only one job per directory runs at a time, and
# retries of that job are serialised by the scheduler.

set -u

NFAILS=$1
MODE=$2
COUNTER=./.oos.count

cur=$(cat "$COUNTER" 2>/dev/null || echo 0)
cur=$((cur + 1))
echo "$cur" > "$COUNTER"

if [ "$cur" -le "$NFAILS" ]; then
  if [ "$MODE" = oos ]; then
    echo "Run out of store - interrupting threads" >&2
    echo "Exception- Interrupt raised"
  else
    echo "oos.sh: deliberate failure number $cur" >&2
  fi
  exit 1
fi

echo "oos.sh: succeeded on attempt $cur"
exit 0
