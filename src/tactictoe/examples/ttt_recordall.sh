#!/usr/bin/env bash
# ===========================================================================
# FILE          : ttt_recordall.sh
# DESCRIPTION   : Record a TacticToe tactic database for the ENTIRE HOL4
#                 standard library.
#
# Runs the companion script ttt_recordall.sml under hol, which loads
# every theory in $HOLDIR/sigobj (the whole standard library) via
# aiLib.load_sigobj () and then records tactic data for all of them via
# tttUnfold.ttt_record ().
#
# Prerequisites:
#   * HOLDIR exported to point at a built HOL4 tree (see below).
#   * A full HOL4 build so that $HOLDIR/sigobj is populated:
#       bin/build -F
#   * Recording opens many files; the script raises the soft open-file
#     limit to 20000 (as recommended by src/tactictoe/EVALUATION).  If
#     the hard limit is lower than 20000, raise it first in the shell
#     that launches this script (e.g. via ulimit -Hn).
#
# Usage:
#   export HOLDIR=/path/to/HOL
#   ./src/tactictoe/examples/ttt_recordall.sh
#   ./src/tactictoe/examples/ttt_recordall.sh --keep
#   ./src/tactictoe/examples/ttt_recordall.sh --output /path/to/out
#   ./src/tactictoe/examples/ttt_recordall.sh --output /path/to/out \
#       --keep
#
# Output:
#   By default the tactic database is written to
#     $HOLDIR/src/tactictoe/ttt_tacdata
#   (that path is hard-coded in mlTacticData.sml / tttSetup.sml).  Use
#   --output DIR to redirect it: the script symlinks
#   $HOLDIR/src/tactictoe/ttt_tacdata -> DIR before recording.
#   Scratch temp dirs (src/AI/sml_inspection/{open,buildheap},
#   src/tactictoe/info, src/tactictoe/code) are NOT redirected and
#   stay under $HOLDIR; they are cleaned up by this script.
# ===========================================================================

set -euo pipefail

# --- help ------------------------------------------------------------------
usage() {
  sed -n '2,46p' "${BASH_SOURCE[0]}"
}

# --- parse arguments (before any environment checks) ----------------------
keep=0
output_dir=""
while [ $# -gt 0 ]; do
  case "$1" in
    --keep) keep=1; shift ;;
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

if [ ! -x "${hol_bin}" ]; then
  echo "error: hol binary not found at ${hol_bin}" >&2
  echo "       is HOLDIR (${HOLDIR}) a built HOL4 tree?" >&2
  exit 1
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
  echo "       build HOL4 first:  bin/build -F" >&2
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
# The tactic database path is hard-coded in the SML sources to
# $HOLDIR/src/tactictoe/ttt_tacdata, so redirection is done by symlinking
# that path to the user's --output directory.
tacdata_path="${hol_dir}/src/tactictoe/ttt_tacdata"
skip_clean_in_sml=0   # 1 => strip ttt_clean_record () from the SML feed

if [ -n "${output_dir}" ]; then
  # Resolve to an absolute path (for a stable symlink target).
  if [ ! -d "${output_dir}" ]; then
    echo "creating output directory: ${output_dir}"
    mkdir -p "${output_dir}"
  fi
  output_dir="$(cd "${output_dir}" && pwd)"

  if [ -e "${tacdata_path}" ] && [ ! -L "${tacdata_path}" ]; then
    echo "error: ${tacdata_path} already exists and is not a symlink." >&2
    echo "       --output requires that path to be absent or a symlink" >&2
    echo "       so it can be repointed at ${output_dir}." >&2
    echo "       Remove or rename the existing directory first." >&2
    exit 1
  fi

  if [ -L "${tacdata_path}" ]; then
    cur="$(readlink -f "${tacdata_path}" || true)"
    if [ "${cur}" = "${output_dir}" ]; then
      echo "output symlink already points at ${output_dir}"
    else
      echo "repointing ${tacdata_path} -> ${output_dir}"
      rm -f "${tacdata_path}"
      ln -s "${output_dir}" "${tacdata_path}"
    fi
  else
    echo "symlinking ${tacdata_path} -> ${output_dir}"
    ln -s "${output_dir}" "${tacdata_path}"
  fi

  # ttt_clean_record () would `rm -r` the symlink and recreate it as a
  # real directory, undoing the redirection.  Clean from the shell
  # instead and strip that call from the SML feed.
  skip_clean_in_sml=1
fi

# --- decide whether the SML feed should clean first ------------------------
if [ "${keep}" -eq 1 ] || [ "${skip_clean_in_sml}" -eq 1 ]; then
  feed="$(grep -v 'ttt_clean_record ();' "${sml_file}")"
else
  feed="$(cat "${sml_file}")"
fi

if [ "${keep}" -eq 1 ]; then
  echo "--keep: preserving existing tactic data; only recording"
  echo "         theories not yet recorded."
else
  # Wipe the tactic database and scratch temp dirs.
  if [ "${skip_clean_in_sml}" -eq 1 ]; then
    echo "cleaning output directory contents: ${output_dir}"
    if [ -d "${output_dir}" ]; then
      find "${output_dir}" -mindepth 1 -delete
    fi
  else
    echo "cleaning tactic database: ${tacdata_path}"
  fi
  # Clean the scratch temp dirs (ttt_clean_temp targets) that exist
  # before recording; recreate the empty ones so ttt_record_thy starts
  # fresh.  These are not redirected and live under $HOLDIR.
  for d in \
      "${hol_dir}/src/AI/sml_inspection/open" \
      "${hol_dir}/src/AI/sml_inspection/buildheap" \
      "${hol_dir}/src/tactictoe/info"; do
    if [ -d "${d}" ]; then
      rm -rf "${d}"
    fi
    mkdir -p "${d}"
  done
fi

# Scratch dirs removed after hol finishes (the recording creates them).
# src/tactictoe/code is written by aiLib.sigobj_theories () during
# load_sigobj () and is not needed once recording is done.
post_run_scratch=(
  "${hol_dir}/src/AI/sml_inspection/open"
  "${hol_dir}/src/AI/sml_inspection/buildheap"
  "${hol_dir}/src/tactictoe/info"
  "${hol_dir}/src/tactictoe/code"
)
cleanup_scratch() {
  local d
  for d in "${post_run_scratch[@]}"; do
    if [ -d "${d}" ]; then
      rm -rf "${d}"
    fi
  done
}

# --- run hol ---------------------------------------------------------------
echo
echo "Starting hol to record tactic data for the whole"
echo "standard library."
echo "Output: ${tacdata_path}"
echo

# `hol run` evaluates an SML file for side effects.  It rejects
# /dev/stdin (it looks for a matching .ui file), so write the feed to a
# temp file and clean it up on exit.  mktemp with a bare template returns
# a relative path, so resolve it to absolute (we must not `cd` away from
# it before invoking hol).
tmp_sml="$(mktemp --suffix=.sml ttt_recordall.XXXXXX)"
tmp_sml="$(readlink -f "${tmp_sml}")"
# Capture hol's exit status so the script can propagate it, then clean up
# the temp file and recording scratch dirs (including src/tactictoe/code,
# created during recording) on exit -- whether hol succeeded, failed, or
# was interrupted.
hol_rc=0
trap 'rm -f "${tmp_sml}"; cleanup_scratch' EXIT
printf '%s\n' "${feed}" > "${tmp_sml}"

"${hol_bin}" run "${tmp_sml}" || hol_rc=$?
exit ${hol_rc}
