#!/bin/sh
set -eu

if [ "$#" -ne 3 ]; then
  echo "usage: tests/run.sh TEST /path/to/tracing/bin/hol /scratch/dir" >&2
  echo "TEST: all, identity, oracle, export, numeral, compute-binder, term-kind" >&2
  exit 2
fi
pft_test=$1
pft_hol=$2
pft_scratch=$3
pft_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
HOL_PFT_SOURCE_ROOT=$(CDPATH= cd -- "$pft_dir/../../../.." && pwd)
export HOL_PFT_SOURCE_ROOT
case "$pft_test" in
  all) pft_suites='identity oracle export numeral compute-binder term-kind' ;;
  identity|oracle|export|numeral|compute-binder|term-kind) pft_suites=$pft_test ;;
  *) echo "unknown prooftrace test: $pft_test" >&2; exit 2 ;;
esac
mkdir -p "$pft_scratch"
pft_scratch=$(CDPATH= cd -- "$pft_scratch" && pwd)
for HOL_PFT_TEST in $pft_suites; do
  export HOL_PFT_TEST
  mkdir -p "$pft_scratch/$HOL_PFT_TEST/.hol/objs" \
           "$pft_scratch/$HOL_PFT_TEST/hol4"
  cd "$pft_scratch/$HOL_PFT_TEST"
  case "$HOL_PFT_TEST" in
    identity) pft_phases='produce import-parent import-child convert raw separate merged role custom-role' ;;
    export) pft_phases='vacuous shadow overlap' ;;
    *) pft_phases=run ;;
  esac
  for HOL_PFT_IDENTITY_PHASE in $pft_phases; do
    export HOL_PFT_IDENTITY_PHASE
    HOL_PFT_EXPORT_CASE=$HOL_PFT_IDENTITY_PHASE
    export HOL_PFT_EXPORT_CASE
    case "$HOL_PFT_TEST:$HOL_PFT_IDENTITY_PHASE" in
      identity:raw|identity:separate|identity:merged|identity:role|identity:custom-role)
        set -- --min ;;
      *) set -- ;;
    esac
    pft_log=$HOL_PFT_IDENTITY_PHASE.log
    if ! "$pft_hol" run "$@" "$pft_dir/driver.sml" > "$pft_log" 2>&1 ||
       ! grep -q '^PFT_TEST_PHASE_PASS$' "$pft_log"; then
      tail -40 "$pft_log" >&2
      exit 1
    fi
  done
  printf '%s\n' "PFT_TEST_PASS $HOL_PFT_TEST"
done
