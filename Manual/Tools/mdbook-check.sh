#!/usr/bin/env bash
#
# Sanity check the rendered mdbook output for raw-LaTeX patterns
# that should never appear in the published HTML.
#
# Operates on the *rendered* HTML (not the .smd source).  This is
# the lazy-and-correct approach: if a problem reaches the HTML,
# the user will see it, so check there directly rather than
# parsing markdown / LaTeX / SML to predict whether it will.
#
# Usage: mdbook-check.sh <book-dir>
#         e.g. mdbook-check.sh Manual/book/Description
#
# Exits non-zero if any pattern matches; prints a hit list.

set -eu

book=${1:?usage: mdbook-check.sh <book-dir>}

if ! [ -d "$book" ]; then
  echo "mdbook-check: $book is not a directory" >&2
  exit 1
fi

fail=0

# Lines containing $ are MathJax math contexts where \texttt /
# \mathit / etc. are *legitimate* — they'll be rendered client-side
# by MathJax.  We skip those.  Lines that mention MathJax (the
# theme/index.hbs config block in each chapter's <head>) are also
# skipped, since they contain literal `\\mathit{...}` etc. as JS
# string contents.  The worda:/wordb:/wordc: tokens are the
# MathJax-macro keys for theories.smd's \worda/\wordb/\wordc
# (defined in theme/index.hbs in the chapter <head>): the
# definition lines mention `\mathit{...}` as the macro body and
# would otherwise trip the trapped-math check below.
#
# This is rough but practical: in our chapters there's no prose
# line that contains a stray `$` without being math.
filter='\$|MathJax|worda:|wordb:|wordc:|term:|type:|holtxt:'

# (pattern, description) pairs.  Patterns are ERE.  Backslashes:
# bash single quotes pass through verbatim, so `\\X` in source =
# `\\X` to grep -E = the literal text `\X`.
check() {
  local pattern=$1 description=$2 f
  for f in "$book"/*.html; do
    [ -e "$f" ] || continue
    case "$(basename "$f")" in print.html) continue ;; esac
    local hits
    hits=$(grep -nE "$pattern" "$f" 2>/dev/null \
              | grep -Ev "$filter" || true)
    if [ -n "$hits" ]; then
      echo "$f: $description"
      printf '%s\n' "$hits" | head -3 | sed 's|^|  |'
      fail=1
    fi
  done
}

# Raw LaTeX text commands that should never reach mdbook HTML.
check '\\texttt\{'        'raw \texttt{} leak'
check '\\textbar([^a-z]|$)' 'raw \textbar leak'
check '\\textasciitilde'  'raw \textasciitilde leak'
check '\\begin\{table\}'  'raw \begin{table} leak'
check '\\end\{table\}'    'raw \end{table} leak'
check '\\ref\{'           'unresolved \ref{}'
check '\\label\{'         'unstripped \label{}'

# Double-backslash math signatures.  When `$$\mathit{...}$$` reaches
# smdpp's protectMath pass it becomes `$$\\mathit{...}$$` (escaped
# for MathJax).  If pulldown-cmark then puts that in a <pre><code>
# block (e.g. because the $$ was indented inside a definition-list
# body), the escaped form ends up as literal text in the HTML.
# The double-backslash form is the unique signature of that bug.
check '\\\\(mathit|mathtt|texttt|textbf|textit)\{' \
      'math content trapped in code block (escaped \\X{...})'

if [ "$fail" -ne 0 ]; then
  echo "mdbook-check: rendered-HTML leaks detected (see hits above)." >&2
  exit 1
fi
echo "mdbook-check: OK"
