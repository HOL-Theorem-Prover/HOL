#!/usr/bin/env bash
#
# perf-regression.sh -- compare per-script build times between two HOL4 refs.
#
# Usage:  developers/perf-regression.sh [options] REF_A REF_B
#
# For each ref, if a cached log exists under
#   tools/build-logs/perfcache/<full-sha>.log
# it is reused; otherwise a throw-away `git worktree add` is used to
# check the ref out, `poly < tools/smart-configure.sml` is run there,
# `bin/build -F -t3` (the default) builds it, and the timing log
# emitted into that worktree's `tools/build-logs/` is copied into the
# cache under the resolved commit SHA.
#
# Once both logs are on hand, `git diff --name-only REF_A REF_B --
# '*Script.sml'` selects the scripts that changed between the refs;
# their corresponding *Theory rows are filtered out of both logs
# before the pair is fed to `bin/comparelogs -d`.
#
# The cache is keyed only on the resolved commit SHA, so times remain
# valid across invocations as long as the host and toolchain (Poly/ML,
# system libraries) don't change under the cache.  If they do, remove
# the affected .log files from the cache.

set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd -P)
holdir=$(cd "$script_dir/.." && pwd -P)

usage() {
    cat <<EOF
Usage: $0 [options] REF_A REF_B

Compare per-script build times between two HOL4 refs (SHAs, branches,
tags).  Refs are resolved to commit SHAs via 'git rev-parse'.

Options:
  --core            build only up to src/parallel_builds/ per ref
                    (bin/build -t --seq=tools/sequences/upto-parallel);
                    default is a full build with 'bin/build -F -t3'
  --refresh         rebuild for both refs even if their logs are cached
  --refresh-a       rebuild for REF_A only
  --refresh-b       rebuild for REF_B only
  --cache DIR       cache directory for per-SHA logs
                    (default: tools-poly/build-logs/perfcache)
  --scratch DIR     where kept worktrees are moved after the build
                    (default: <cache-dir>/wt); only relevant with
                    --keep-worktrees
  --keep-worktrees  after each build, move the worktree from its
                    temporary location under \$TMPDIR to
                    <scratch-dir>/<sha> instead of removing it
  --include-changed compare rows even for theories whose *Script.sml
                    differs between the refs (by default they are
                    omitted, since their build times aren't comparable)
  -h, --help        show this help

The build worktree is always created under \$TMPDIR so an outer
holproject.toml at HOLDIR doesn't leak into the build.  The cache
dir defaults under tools-poly/build-logs/, which is git-ignored.
EOF
    exit "${1:-0}"
}

build_mode=full
refresh_a=
refresh_b=
keep_wt=
include_changed=
cache_dir="$holdir/tools-poly/build-logs/perfcache"
scratch_dir=

while [ $# -gt 0 ]; do
    case $1 in
        --core)             build_mode=core; shift ;;
        --refresh)          refresh_a=1; refresh_b=1; shift ;;
        --refresh-a)        refresh_a=1; shift ;;
        --refresh-b)        refresh_b=1; shift ;;
        --cache)            cache_dir=$2; shift 2 ;;
        --scratch)          scratch_dir=$2; shift 2 ;;
        --keep-worktrees)   keep_wt=1; shift ;;
        --include-changed)  include_changed=1; shift ;;
        -h|--help)          usage 0 ;;
        --)                 shift; break ;;
        -*)                 echo "Unknown option: $1" >&2; usage 1 ;;
        *)                  break ;;
    esac
done

if [ $# -ne 2 ]; then
    echo "Expected exactly two refs; got $#." >&2
    usage 1
fi

ref_a=$1
ref_b=$2

: "${scratch_dir:=$cache_dir/wt}"

# absolutise both dirs so they survive the cd into each worktree
mkdir -p "$cache_dir" "$scratch_dir"
cache_dir=$(cd "$cache_dir" && pwd -P)
scratch_dir=$(cd "$scratch_dir" && pwd -P)

comparelogs="$holdir/bin/comparelogs"
if [ ! -x "$comparelogs" ]; then
    echo "error: $comparelogs not found or not executable." >&2
    echo "Run 'poly < tools/smart-configure.sml' in $holdir first." >&2
    exit 1
fi

resolve_sha() {
    local ref=$1
    local sha
    if ! sha=$(git -C "$holdir" rev-parse --verify --quiet "$ref^{commit}"); then
        echo "error: ref not found in $holdir: $ref" >&2
        exit 1
    fi
    printf '%s\n' "$sha"
}

sha_a=$(resolve_sha "$ref_a")
sha_b=$(resolve_sha "$ref_b")

echo "REF_A: $ref_a -> $sha_a"
echo "REF_B: $ref_b -> $sha_b"

case $build_mode in
    full) build_argv=(-F -t3) ;;
    core) build_argv=(-t --seq=tools/sequences/upto-parallel) ;;
esac

# Build a fresh log for one SHA into $cache_dir/${build_mode}-$sha.log.
# The worktree is created under $TMPDIR so Holmake in the build tree
# doesn't discover HOLDIR's holproject.toml by walking up.  With
# --keep-worktrees the tree is moved to $scratch_dir/$sha after the
# build; otherwise it's removed.
build_at_sha() {
    local sha=$1
    local target="$cache_dir/${build_mode}-$sha.log"

    local tmpparent wt
    tmpparent=$(mktemp -d)
    wt="$tmpparent/wt"

    echo
    echo "== Building $sha in $wt =="

    git -C "$holdir" worktree add --detach "$wt" "$sha"

    local before after
    before=$(mktemp)
    after=$(mktemp)
    ls -1 "$wt/tools-poly/build-logs" 2>/dev/null | sort > "$before" || true

    (
        cd "$wt"
        poly < tools/smart-configure.sml
        bin/build "${build_argv[@]}"
    )

    ls -1 "$wt/tools-poly/build-logs" | sort > "$after"

    # A successful build renames current-build-log to
    # <host><timestamp>[-kernel]; that's the one new file we want.
    local newlog
    newlog=$(comm -13 "$before" "$after" \
             | grep -v '^current-build-log$' \
             | grep -v '^perfcache$' \
             | head -n1 || true)
    if [ -z "$newlog" ]; then
        echo "error: build finished but no new log appeared under" >&2
        echo "  $wt/tools-poly/build-logs/" >&2
        echo "(bin/build normally renames current-build-log on success)." >&2
        exit 1
    fi

    cp "$wt/tools-poly/build-logs/$newlog" "$target"
    echo "Cached log for $sha at $target"

    rm -f "$before" "$after"

    if [ -n "$keep_wt" ]; then
        local keep_dir="$scratch_dir/$sha"
        if [ -e "$keep_dir" ]; then
            git -C "$holdir" worktree remove --force "$keep_dir" 2>/dev/null \
              || rm -rf "$keep_dir"
        fi
        git -C "$holdir" worktree move "$wt" "$keep_dir"
        echo "Kept worktree at $keep_dir"
    else
        git -C "$holdir" worktree remove --force "$wt"
    fi
    rmdir "$tmpparent" 2>/dev/null || true
}

ensure_log() {
    local sha=$1
    local refresh=$2
    if [ -n "$refresh" ] || [ ! -f "$cache_dir/${build_mode}-$sha.log" ]; then
        build_at_sha "$sha"
    else
        echo "Using cached log for $sha at $cache_dir/${build_mode}-$sha.log"
    fi
}

ensure_log "$sha_a" "$refresh_a"
ensure_log "$sha_b" "$refresh_b"

tmpdir=$(mktemp -d)
trap 'rm -rf "$tmpdir"' EXIT

exclude_file="$tmpdir/excluded-theories"
echo
if [ -n "$include_changed" ]; then
    : > "$exclude_file"
    echo "Not omitting theories with changed scripts (--include-changed)."
else
    # Log keys are <rel-path-from-HOLDIR>/<bare-thyname> (no "Theory" suffix,
    # see maybe_log_time_to_disk in src/postkernel/Theory.sml); rewrite each
    # changed *Script.sml path into that form so filter_log's $1-lookup matches.
    git -C "$holdir" diff --name-only "$sha_a" "$sha_b" -- '*Script.sml' \
      | awk 'sub(/Script\.sml$/, "")' \
      | sort -u > "$exclude_file"

    n_excluded=$(wc -l < "$exclude_file" | tr -d ' ')
    if [ "$n_excluded" -gt 0 ]; then
        echo "Excluding $n_excluded script(s) whose *Script.sml changed between refs:"
        sed 's/^/  /' "$exclude_file"
    else
        echo "No *Script.sml files changed between refs; comparing all rows."
    fi
fi

filter_log() {
    # tools/Holmake/tests/** theories are always dropped: Holmake
    # selftests build them repeatedly during one bin/build run, which
    # comparelogs then poisons as duplicate entries.
    #
    # An empty exclude_file breaks the 'NR==FNR' idiom (awk keeps NR=FNR
    # when a file yields no records), so short-circuit on the empty case.
    if [ -s "$exclude_file" ]; then
        awk 'NR==FNR { skip[$1]=1; next }
             $1 ~ /^tools\/Holmake\/tests\// { next }
             !($1 in skip)' \
            "$exclude_file" "$1" > "$2"
    else
        awk '$1 !~ /^tools\/Holmake\/tests\//' "$1" > "$2"
    fi
}

sname_a="${sha_a:0:12}"
sname_b="${sha_b:0:12}"
if [ "$sname_a" = "$sname_b" ]; then
    sname_a="A-$sname_a"
    sname_b="B-$sname_b"
fi
filtered_a="$tmpdir/$sname_a.log"
filtered_b="$tmpdir/$sname_b.log"
filter_log "$cache_dir/${build_mode}-$sha_a.log" "$filtered_a"
filter_log "$cache_dir/${build_mode}-$sha_b.log" "$filtered_b"

echo
"$comparelogs" -d "$filtered_a" "$filtered_b"
