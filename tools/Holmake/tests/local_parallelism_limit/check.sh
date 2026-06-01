#!/bin/sh
# check.sh LIMIT TAG
#
# Atomically increment a shared counter under flock; if the counter
# exceeds LIMIT after the increment, this invocation is concurrent
# with too many of its peers and exits non-zero so the build fails.
# Otherwise sleep briefly (to widen the overlap window) and decrement.
#
# The TAG argument is part of the command line so each rule has a
# distinct command — otherwise Holmake's same-command de-duplication
# would treat all targets as a single job.
#
# Counter / lockfile live in CWD so each test subdirectory has its
# own pair.

set -u

LIMIT=$1
TAG=$2  # unused except to make this rule's command unique
LOCK=./.plimit.lock
COUNTER=./.plimit.count

(
  flock -x 9
  cur=$(cat "$COUNTER" 2>/dev/null || echo 0)
  cur=$((cur + 1))
  echo "$cur" > "$COUNTER"
  if [ "$cur" -gt "$LIMIT" ]; then
    echo "LOCAL_PARALLELISM_LIMIT VIOLATION: $cur > $LIMIT in $(pwd) at $TAG" >&2
    exit 1
  fi
) 9>"$LOCK" || exit 1

sleep 0.2

(
  flock -x 9
  cur=$(cat "$COUNTER" 2>/dev/null || echo 0)
  cur=$((cur - 1))
  echo "$cur" > "$COUNTER"
) 9>"$LOCK"

exit 0
