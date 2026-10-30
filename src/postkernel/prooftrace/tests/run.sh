#!/bin/sh
set -eu

if [ "$#" -ne 3 ] || [ "$1" != identity ]; then
  echo "usage: tests/run.sh identity /path/to/tracing/bin/hol /scratch/dir" >&2
  exit 2
fi
pft_hol=$2
pft_scratch=$3
pft_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
HOL_PFT_SOURCE_ROOT=$(CDPATH= cd -- "$pft_dir/../../../.." && pwd)
export HOL_PFT_SOURCE_ROOT
mkdir -p "$pft_scratch/identity/.hol/objs"
cd "$pft_scratch/identity"
pft_phases="produce loader-parent loader-child raw"
for HOL_PFT_IDENTITY_PHASE in $pft_phases; do
  export HOL_PFT_IDENTITY_PHASE
  case "$HOL_PFT_IDENTITY_PHASE" in
    produce) set -- ;;
    *) set -- --min ;;
  esac
  pft_log=$HOL_PFT_IDENTITY_PHASE.log
  if ! "$pft_hol" run "$@" "$pft_dir/driver.sml" > "$pft_log" 2>&1 ||
     ! grep -q '^PFT_TEST_PHASE_PASS$' "$pft_log"; then
    tail -40 "$pft_log" >&2
    exit 1
  fi
done
printf '%s\n' 'PFT_TEST_PASS identity'
