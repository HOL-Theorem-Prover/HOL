#!/bin/sh
set -eu

if [ "$#" -ne 2 ]; then
  echo "usage: identity-tests.sh /path/to/tracing/bin/hol /scratch/dir" >&2
  exit 2
fi
identity_hol=$1
identity_scratch=$2
identity_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
HOL_PFT_SOURCE_ROOT=$(CDPATH= cd -- "$identity_dir/../../.." && pwd)
export HOL_PFT_SOURCE_ROOT
mkdir -p "$identity_scratch/.hol/objs" "$identity_scratch/hol4"
cd "$identity_scratch"

for HOL_PFT_IDENTITY_PHASE in produce import-parent import-child convert \
                              raw separate merged role custom-role; do
  export HOL_PFT_IDENTITY_PHASE
  case "$HOL_PFT_IDENTITY_PHASE" in
    produce|import-parent|import-child|convert) identity_heap= ;;
    *) identity_heap=--min ;;
  esac
  if ! "$identity_hol" run $identity_heap "$identity_dir/identity-driver.sml" \
      > "$HOL_PFT_IDENTITY_PHASE.log" 2>&1; then
    tail -40 "$HOL_PFT_IDENTITY_PHASE.log" >&2
    exit 1
  fi
done
printf '%s\n' 'IDENTITY_FOCUSED_TESTS_PASS'
