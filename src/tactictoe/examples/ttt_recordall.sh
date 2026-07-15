#!/usr/bin/env bash
# ===========================================================================
# FILE          : ttt_recordall.sh
# DESCRIPTION   : Record a TacticToe tactic database for the ENTIRE HOL4
#                 standard library.
#
# Runs the companion script ttt_recordall.sml under hol, which loads
# every theory in $HOLDIR/sigobj (the whole standard library) via
# tttUnfold.load_sigobj () and then records tactic data for all of them via
# tttUnfold.ttt_record ().
#
# Prerequisites:
#   * HOLDIR exported to point at a built HOL4 tree (see below).
#   * The script runs a full HOL4 build (`bin/build -F`) to populate
#     $HOLDIR/sigobj before recording.  Pass --no-build to skip this
#     (e.g. for a re-run after a successful full build).
#   * Recording opens many files; the script raises the soft open-file
#     limit to 20000 (as recommended by src/tactictoe/EVALUATION).  If
#     the hard limit is lower than 20000, raise it first in the shell
#     that launches this script (e.g. via ulimit -Hn).
# Usage:
#   export HOLDIR=/path/to/HOL
#   ./src/tactictoe/examples/ttt_recordall.sh
#   ./src/tactictoe/examples/ttt_recordall.sh --no-build
#   ./src/tactictoe/examples/ttt_recordall.sh --keep
#   ./src/tactictoe/examples/ttt_recordall.sh --output /path/to/out
#   ./src/tactictoe/examples/ttt_recordall.sh --output /path/to/out \
#       --keep
#
# Output:
#   By default the tactic database is written to HOL4_TACTICTOE_CACHE when
#   that variable is set, otherwise under XDG_CACHE_HOME when set, and
#   finally under $HOME/.cache:
#     ${XDG_CACHE_HOME:-$HOME/.cache}/tactictoe/ttt_tacdata
#   Use --output DIR to use DIR as the TacticToe cache root instead
#   (the tactic database will be written to DIR/ttt_tacdata).
#   The script exports HOL4_TACTICTOE_CACHE for the hol process; HOLDIR
#   is used only to find/read the HOL installation and to run bin/hol.
# ===========================================================================

set -euo pipefail

# --- memory/cgroup diagnostics ---------------------------------------------
fmt_mem() {
  if [ "$1" = "max" ]; then
    printf 'max'
  elif command -v numfmt >/dev/null 2>&1; then
    numfmt --to=iec --suffix=B "$1"
  else
    printf '%s bytes' "$1"
  fi
}

print_memory_cgroup() {
  local cg cur part val effective
  cg=""
  if [ -r /proc/self/cgroup ]; then
    cg="$(awk -F: '$1 == "0" { print $3; exit }' /proc/self/cgroup)"
  fi
  [ -n "${cg}" ] || cg="/"

  echo "Memory/cgroup diagnostics:"
  echo "  cgroup: ${cg}"

  if [ ! -d /sys/fs/cgroup ]; then
    echo "  /sys/fs/cgroup not found"
    return
  fi

  cur="/sys/fs/cgroup"
  effective="max"
  if [ -r "${cur}/memory.max" ]; then
    val="$(cat "${cur}/memory.max")"
    if [ "${val}" != "max" ]; then effective="${val}"; fi
  fi

  IFS='/' read -r -a parts <<< "${cg#/}"
  for part in "${parts[@]}"; do
    [ -n "${part}" ] || continue
    cur="${cur}/${part}"
    if [ -r "${cur}/memory.max" ]; then
      val="$(cat "${cur}/memory.max")"
      if [ "${val}" != "max" ] &&
         { [ "${effective}" = "max" ] ||
           [ "${val}" -lt "${effective}" ]; }; then
        effective="${val}"
      fi
    fi
  done

  if [ -r "${cur}/memory.max" ]; then
    echo "  memory.max here: $(fmt_mem "$(cat "${cur}/memory.max")")"
  fi
  echo "  effective memory.max: $(fmt_mem "${effective}")"
  if [ -r "${cur}/memory.current" ]; then
    echo "  memory.current: $(fmt_mem "$(cat "${cur}/memory.current")")"
  fi
  if [ -r "${cur}/memory.peak" ]; then
    echo "  memory.peak: $(fmt_mem "$(cat "${cur}/memory.peak")")"
  fi
  if [ -r "${cur}/memory.swap.max" ]; then
    echo "  memory.swap.max: $(fmt_mem "$(cat "${cur}/memory.swap.max")")"
  fi
}

print_memory_cgroup

# --- help ------------------------------------------------------------------
usage() {
  cat <<'EOF'
Record a TacticToe tactic database for the ENTIRE HOL4 standard library.

Runs the companion script ttt_recordall.sml under hol, which loads every
theory in $HOLDIR/sigobj (the whole standard library) via
tttUnfold.load_sigobj () and then records tactic data for all of them via
tttUnfold.ttt_record ().

Usage:
  export HOLDIR=/path/to/HOL
  ttt_recordall.sh [--no-build] [--keep] [--output DIR]

  --no-build    Skip the full HOL4 build; record from the current sigobj.
                By default a `bin/build -F` runs first, to populate sigobj.
  --keep        Keep existing tactic data: only record theories that are
                missing or stale.  Without it the cache is wiped first.
  --output DIR  Use DIR as the TacticToe cache root instead of
                HOL4_TACTICTOE_CACHE (when set),
                $XDG_CACHE_HOME/tactictoe (when set), or
                $HOME/.cache/tactictoe.
                The tactic database is written to DIR/ttt_tacdata and DIR is
                exported to hol as HOL4_TACTICTOE_CACHE.

Recording opens many files; the script raises the soft open-file limit to
20000 (as recommended by src/tactictoe/EVALUATION).  If the hard limit is
lower than 20000, raise it first in the launching shell (ulimit -Hn 20000).
EOF
}

# --- parse arguments (before any environment checks) ----------------------
keep=0
output_dir=""
no_build=0
while [ $# -gt 0 ]; do
  case "$1" in
    --keep) keep=1; shift ;;
    --no-build) no_build=1; shift ;;
    -h|--help) usage; exit 0 ;;
    --output)
      if [ $# -lt 2 ]; then
        echo "error: --output requires an argument" >&2
        exit 2
      fi
      output_dir="$2"; shift 2 ;;
    --output=*) output_dir="${1#--output=}"; shift ;;
    *)
      echo "unknown argument: $1" >&2
      exit 2
      ;;
  esac
done

# --- locate the HOL tree ---------------------------------------------------
# HOLDIR must point at a built HOL4 tree (the same env var the HOL4
# tooling uses).  Export it before running this script.
if [ -z "${HOLDIR:-}" ]; then
  echo "error: HOLDIR is not set" >&2
  echo "       export HOLDIR to point at a built HOL4 tree" >&2
  echo "       (build first with: bin/build -F)" >&2
  exit 1
fi
hol_dir="${HOLDIR}"
hol_bin="${hol_dir}/bin/hol"
build_bin="${hol_dir}/bin/build"

if [ ! -x "${hol_bin}" ]; then
  echo "error: hol binary not found at ${hol_bin}" >&2
  echo "       is HOLDIR (${HOLDIR}) a built HOL4 tree?" >&2
  exit 1
fi

# --- full build (populates $HOLDIR/sigobj with the whole stdlib) ----------
if [ "${no_build}" -eq 1 ]; then
  echo "--no-build: skipping build; recording from the current sigobj."
else
  echo "Running full HOL4 build to populate ${hol_dir}/sigobj:"
  echo "  ${build_bin} -F"
  if [ ! -x "${build_bin}" ]; then
    echo "error: build binary not found at ${build_bin}" >&2
    exit 1
  fi
  "${build_bin}" -F
  echo "build finished."
fi

# src/tactictoe/examples/ lives in the HOL4 tree; find it relative to
# this script so the companion .sml file can be located regardless of
# the current directory.
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# --- sanity: sigobj must be populated --------------------------------------
sigobj_dir="${hol_dir}/sigobj"
if [ ! -d "${sigobj_dir}" ] ||
   ! ls "${sigobj_dir}"/*Theory.sig >/dev/null 2>&1; then
  echo "error: no *Theory.sig files under ${sigobj_dir}" >&2
  if [ "${no_build}" -eq 1 ]; then
    echo "       --no-build was given; build HOL4 first:  bin/build -F" >&2
  else
    echo "       the build above should have populated sigobj;" >&2
    echo "       check the build output for failures." >&2
  fi
  exit 1
fi
nthy=$(ls "${sigobj_dir}"/*Theory.sig 2>/dev/null | wc -l)
echo "Found ${nthy} theory signatures in ${sigobj_dir}"

# --- raise the open-file limit (recording opens many files) ----------------
desired=20000
soft=$(ulimit -Sn)
if [ "${soft}" -lt "${desired}" ]; then
  echo "Raising open-file soft limit: ${soft} -> ${desired}"
  if ! ulimit -Sn "${desired}" 2>/dev/null; then
    newsoft=$(ulimit -Sn)
    echo "warning: could not raise soft limit to ${desired};" >&2
    echo "         now at ${newsoft}" >&2
    echo "         (raise the hard limit first, e.g." >&2
    echo "          ulimit -Hn ${desired})" >&2
  fi
fi
echo "open-file soft limit: $(ulimit -Sn), hard limit: $(ulimit -Hn)"

# --- companion SML file -----------------------------------------------------
sml_file="${script_dir}/ttt_recordall.sml"
if [ ! -f "${sml_file}" ]; then
  echo "error: missing ${sml_file}" >&2
  exit 1
fi

# --- set up the output directory -------------------------------------------
if [ -n "${output_dir}" ]; then
  if [ ! -d "${output_dir}" ]; then
    echo "creating output directory: ${output_dir}"
    mkdir -p "${output_dir}"
  fi
  cache_root="$(cd "${output_dir}" && pwd)"
else
  if [ -n "${HOL4_TACTICTOE_CACHE:-}" ]; then
    cache_root="${HOL4_TACTICTOE_CACHE}"
  elif [ -n "${XDG_CACHE_HOME:-}" ]; then
    cache_root="${XDG_CACHE_HOME}/tactictoe"
  elif [ -z "${HOME:-}" ]; then
    echo "error: neither XDG_CACHE_HOME nor HOME is set;" >&2
    echo "       cannot choose default TacticToe cache" >&2
    exit 1
  else
    cache_root="${HOME}/.cache/tactictoe"
  fi
fi
export HOL4_TACTICTOE_CACHE="${cache_root}"
tacdata_path="${cache_root}/ttt_tacdata"
echo "TacticToe cache root: ${HOL4_TACTICTOE_CACHE}"

# --- keep or clean ---------------------------------------------------------
# ttt_recordall.sml reads TTT_RECORDALL_KEEP to decide whether to call
# ttt_clean_record () first.
if [ "${keep}" -eq 1 ]; then
  export TTT_RECORDALL_KEEP=1
  echo "--keep: preserving existing tactic data; only recording missing"
  echo "        or stale theories."
else
  export TTT_RECORDALL_KEEP=0
  echo "cleaning tactic database: ${tacdata_path}"
fi

# --- run hol ---------------------------------------------------------------
echo
echo "Starting hol to record tactic data for the whole"
echo "standard library."
echo "Output: ${tacdata_path}"
echo

exec "${hol_bin}" run "${sml_file}"
