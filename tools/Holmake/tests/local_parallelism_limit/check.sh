#!/bin/sh
# check.sh LIMIT TAG
#
# Atomically increment a shared counter; if the counter exceeds LIMIT
# after the increment, this invocation is concurrent with too many of
# its peers and exits non-zero so the build fails.  Otherwise sleep
# briefly (to widen the overlap window) and decrement.
#
# The TAG argument is part of the command line so each rule has a
# distinct command — otherwise Holmake's same-command de-duplication
# would treat all targets as a single job.
#
# Counter / lock live in CWD so each test subdirectory has its own pair.
#
# Mutual exclusion is by mkdir, which is atomic on any POSIX filesystem
# and needs no tool beyond the shell.  flock would say this more
# directly, but it is a util-linux program that macOS does not ship, and
# its absence was silent: the counter updates then raced, and a lost
# decrement could leave the count high enough that the next increment
# reported a violation that had not happened.  Being a race it only
# showed up under load, so the test passed for months first.

set -u

LIMIT=$1
TAG=$2  # unused except to make this rule's command unique
LOCKDIR=./.plimit.lockdir
COUNTER=./.plimit.count

held=no

release() {
  if [ "$held" = yes ]; then
    held=no
    rmdir "$LOCKDIR" 2>/dev/null
  fi
}

# Holmake kills outstanding jobs when another target fails; don't leave
# the lock behind for the next run to spin on.
trap 'release' EXIT
trap 'release; exit 1' INT TERM

acquire() {
  waited=0
  until mkdir "$LOCKDIR" 2>/dev/null; do
    sleep 0.01
    waited=$((waited + 1))
    if [ "$waited" -gt 500 ]; then
      echo "check.sh: gave up waiting for $LOCKDIR in $(pwd)" >&2
      exit 1
    fi
  done
  held=yes
}

acquire
cur=$(cat "$COUNTER" 2>/dev/null || echo 0)
cur=$((cur + 1))
echo "$cur" > "$COUNTER"
if [ "$cur" -gt "$LIMIT" ]; then
  echo "LOCAL_PARALLELISM_LIMIT VIOLATION: $cur > $LIMIT in $(pwd) at $TAG" >&2
  release
  exit 1
fi
release

sleep 0.2

acquire
cur=$(cat "$COUNTER" 2>/dev/null || echo 0)
cur=$((cur - 1))
echo "$cur" > "$COUNTER"
release

exit 0
