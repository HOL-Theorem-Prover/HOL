#!/bin/sh
set -eu
pft_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
pft_holdir=$(CDPATH= cd -- "$pft_dir/../../.." && pwd)
pft_args=$(mktemp)
trap 'rm -f "$pft_args"' EXIT HUP INT TERM
: > "$pft_args"
for pft_arg do
  printf '%s\000' "$pft_arg" >> "$pft_args"
done
HOL_PFT_ARGS_FILE=$pft_args HOL_PFT_LIB_DIR=$pft_dir \
  "${PFT_HOL:-$pft_holdir/bin/hol}" run --bare "$pft_dir/pft-main.sml"
