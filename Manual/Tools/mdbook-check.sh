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
# Manual/theme/index.hbs config block in each chapter's <head>) are
# also skipped, since they contain literal `\\mathit{...}` etc. as
# JS string contents.  The worda:/wordb:/wordc: tokens are the
# MathJax-macro keys for theories.smd's \worda/\wordb/\wordc
# (defined in Manual/theme/index.hbs in the chapter <head>): the
# definition lines mention `\mathit{...}` as the macro body and
# would otherwise trip the trapped-math check below.
#
# This is rough but practical: in our chapters there's no prose
# line that contains a stray `$` without being math.
filter='\$|MathJax|worda:|wordb:|wordc:|term:|type:|holtxt:|<!--| !--|-->|<code>'

# (pattern, description) pairs.  Patterns are ERE.  Backslashes:
# bash single quotes pass through verbatim, so `\\X` in source =
# `\\X` to grep -E = the literal text `\X`.
check() {
  local pattern=$1 description=$2 use_filter=${3:-yes} f
  for f in "$book"/*.html; do
    [ -e "$f" ] || continue
    case "$(basename "$f")" in print.html) continue ;; esac
    local hits
    if [ "$use_filter" = "yes" ]; then
      hits=$(grep -nE "$pattern" "$f" 2>/dev/null \
                | grep -Ev "$filter" || true)
    else
      hits=$(grep -nE "$pattern" "$f" 2>/dev/null || true)
    fi
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
check '\\cite(\[[^]]*\])?\{' 'unresolved \cite{} (smdpp citation pass)'

# Double-backslash math signatures.  When `$$\mathit{...}$$` reaches
# smdpp's protectMath pass it becomes `$$\\mathit{...}$$` (escaped
# for MathJax).  If pulldown-cmark then puts that in a <pre><code>
# block (e.g. because the $$ was indented inside a definition-list
# body), the escaped form ends up as literal text in the HTML.
# The double-backslash form is the unique signature of that bug.
check '\\\\(mathit|mathtt|texttt|textbf|textit)\{' \
      'math content trapped in code block (escaped \\X{...})'

# Empty rendered code block.  Almost always the trace of a fenced
# block whose body was entirely silent polyscripter directives
# (`>>__`, `##use`, ...): the directives produced no output but the
# surrounding fence delimiters made it through to the HTML.  Skip
# the standard filter -- it would mask the very `<code>` we're
# looking for.
check '<pre><code></code></pre>' \
      'empty rendered code block (likely a fence around silent polyscripter setup)' \
      no

# Pandoc-style raw fenced block (e.g. `{=latex}`) reaching mdbook.
# smdpp should strip these for the HTML pipeline; if one slips
# through, pulldown-cmark emits `class="language-{=fmt}"` on a
# <pre><code>.  Symptom: a code-styled box full of raw LaTeX.
check 'class="language-\{=' \
      '{=fmt} raw block reached mdbook (smdpp didn'"'"'t strip it)'

# Bare LaTeX macro-definition commands in prose.  These belong in
# {=latex} blocks (which smdpp strips); the inside-<code> filter
# above means this check only fires when the macro-def text is
# *not* inside a code element -- i.e. it really reached prose.
check '\\(providecommand|newcommand|renewcommand)\b' \
      'LaTeX macro-definition command leaked into mdbook'

# LaTeX environments named in prose.  Same shape as the macro-def
# check: relies on the <code> filter to ignore legitimate code
# samples that mention these environments.
check '\\begin\{(tikzpicture|figure|center|tabular)\}' \
      'LaTeX environment leaked into mdbook'

# Double-hash URLs.  Our index.hbs sidebar rewrite walks ancestor
# li elements; if it picks up an already-rewritten draft-subsection
# href (which now includes `#anchor`) as the "chapter URL" for an
# inner sub-subsection, the resulting link reads `chap.html#a#b`.
check 'href="[^"]*#[^"]*#'  \
      'double-hash URL (sidebar rewrite picked up an anchored ancestor)'

# Old FA4 webfont icon syntax.  mdbook 0.5.x dropped the
# `<i class="fa fa-…">` form in favour of inline SVG emitted by the
# template's `{{fa}}` Handlebars helper; if FA4 reappears, the
# theme template is stale (icons render blank).
check '<i class="fa fa-' \
      'FA4 webfont icon syntax leaked from theme template'


if [ "$fail" -ne 0 ]; then
  echo "mdbook-check: rendered-HTML leaks detected (see hits above)." >&2
  exit 1
fi
echo "mdbook-check: OK"
