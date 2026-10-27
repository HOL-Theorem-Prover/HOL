#!/bin/sh
set -eu

if [ "$#" -ne 2 ]; then
  echo "usage: term-kind-tests.sh /path/to/tracing/bin/hol /scratch/dir" >&2
  exit 2
fi
term_kind_hol=$1
term_kind_scratch=$2
term_kind_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
HOL_PFT_SOURCE_ROOT=$(CDPATH= cd -- "$term_kind_dir/../../.." && pwd)
export HOL_PFT_SOURCE_ROOT
mkdir -p "$term_kind_scratch/.hol/objs"
cd "$term_kind_scratch"
if ! "$term_kind_hol" run "$term_kind_dir/term-kind-selftest.sml" \
     > term-kind.log 2>&1 ||
   ! grep -q '^TERM_KIND_FOCUSED_TESTS_PASS$' term-kind.log; then
  tail -40 term-kind.log >&2
  exit 1
fi
printf '%s\n' 'TERM_KIND_FOCUSED_TESTS_PASS'
