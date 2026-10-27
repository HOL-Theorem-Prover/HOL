#!/bin/sh
set -eu

if [ "$#" -ne 2 ]; then
  echo "usage: compute-binder-tests.sh /path/to/tracing/bin/hol /scratch/dir" >&2
  exit 2
fi
compute_hol=$1
compute_scratch=$2
compute_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
HOL_PFT_SOURCE_ROOT=$(CDPATH= cd -- "$compute_dir/../../.." && pwd)
export HOL_PFT_SOURCE_ROOT
mkdir -p "$compute_scratch/.hol/objs"
cd "$compute_scratch"
if ! "$compute_hol" run "$compute_dir/compute-binder-selftest.sml" \
     > compute-binder.log 2>&1 ||
   ! grep -q '^COMPUTE_BINDER_FOCUSED_TESTS_PASS$' compute-binder.log; then
  tail -40 compute-binder.log >&2
  exit 1
fi
printf '%s\n' 'COMPUTE_BINDER_FOCUSED_TESTS_PASS'
