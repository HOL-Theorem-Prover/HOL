#!/usr/bin/env bash
#
# Static check of .smd source files for raw-LaTeX patterns that
# would leak into the mdbook output if not wrapped properly.
# Run on the worktree; no build required.
#
# We mask out three legitimate-LaTeX contexts before grepping:
#
#   ``` ... ```   fenced code blocks (polyscripter output, raw
#                 {=latex}/{=mdbook} blocks)
#   $...$  /  $$...$$   inline / display math (MathJax consumes
#                       these client-side, so \texttt and friends
#                       are fine here)
#
# Anything matching the forbidden patterns outside those contexts
# is reported as a hit; the user fixes the source and re-runs.
# Source bugs we don't catch (smdpp \ref / \label resolution
# failures, etc.) are smdpp's responsibility and would be caught
# by smdpp's own tests.
#
# Usage: mdbook-check.sh [<smd-dir>]   (default: cwd)

set -eu

dir=${1:-.}

if ! [ -d "$dir" ]; then
  echo "mdbook-check: $dir is not a directory" >&2
  exit 1
fi

# Emit each input line either verbatim (with $...$ math spans
# stripped) or as a blank line if it's inside a ``` ... ``` fence.
# Blank-line emission preserves source line numbers in grep output.
mask_safe_zones() {
  awk '
    BEGIN          { in_fence = 0 }
    /^```/         { in_fence = !in_fence; print ""; next }
    in_fence       { print ""; next }
                   { gsub(/\$\$[^$]*\$\$/, "")
                     gsub(/\$[^$]*\$/, "")
                     print }
  ' "$1"
}

patterns=(
  '\\texttt\{'
  '\\textbar([^a-z]|$)'
  '\\textasciitilde'
  '\\begin\{table\}'
  '\\end\{table\}'
)
descriptions=(
  'raw \texttt{} -- use markdown `X` or a {=latex} raw block'
  'raw \textbar -- use markdown or a {=latex} raw block'
  'raw \textasciitilde -- use markdown or a {=latex} raw block'
  'raw \begin{table} -- wrap in ```{=latex} ... ```'
  'raw \end{table} -- wrap in ```{=latex} ... ```'
)

fail=0
for f in "$dir"/*.smd; do
  [ -e "$f" ] || continue
  masked=$(mask_safe_zones "$f")
  for i in "${!patterns[@]}"; do
    hits=$(printf %s "$masked" | grep -nE "${patterns[$i]}" || true)
    if [ -n "$hits" ]; then
      echo "$f: ${descriptions[$i]}"
      printf '%s\n' "$hits" | sed 's|^|  |'
      echo
      fail=1
    fi
  done
done

if [ "$fail" -ne 0 ]; then
  echo "mdbook-check: source bugs detected (see hits above)." >&2
  exit 1
fi
echo "mdbook-check: OK"
