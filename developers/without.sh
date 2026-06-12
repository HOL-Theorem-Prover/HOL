#!/usr/bin/env bash
#
# without.sh -- start an interactive shell with one or more executables hidden
#               from PATH.
#
#   usage: without.sh <executable-name> [<executable-name> ...]
#   e.g.   without.sh pandoc mlton
#
# Some tools (pandoc, mlton, mdbook, ...) live in directories like /usr/bin that
# you can't simply drop from PATH, because the C toolchain and everything else
# live there too.  This builds a shadow PATH in which only the directories that
# actually contain a named tool are replaced by a sanitised mirror (symlinks to
# everything except those tools); all other directories are reused untouched.
# It then drops you into an interactive bash whose PATH is that shadow.  Nothing
# system-wide is touched; the temp files are removed when the shell exits.
#
# It launches bash (not $SHELL) on purpose: bash's --rcfile lets us run your
# normal startup files and *then* pin PATH, so a profile/rc that resets PATH
# (the common case -- it's what makes the naive version fail) can't sneak a
# hidden tool back in.  Run it on the host or inside the VM.

set -euo pipefail
shopt -s nullglob

if [ "$#" -lt 1 ]; then
  echo "usage: $(basename "$0") <executable-name> [<executable-name> ...]" >&2
  exit 2
fi
tools=("$@")
ntools=${#tools[@]}

farm=$(mktemp -d "${TMPDIR:-/tmp}/without.XXXXXX")
rc=$(mktemp "${TMPDIR:-/tmp}/without-rc.XXXXXX")
trap 'rm -rf "$farm" "$rc"' EXIT

# Build the shadow PATH.  Only dirs that hold a named tool get mirrored (bulk
# symlink into a fresh dir, then delete the tools); the rest are reused as-is.
# So the usual case -- a tool in one or two dirs -- stays near-instant even
# though /usr/bin has thousands of entries.
IFS=: read -ra dirs <<< "$PATH"
total=${#dirs[@]}
parts=()
seen=(); for ((j = 0; j < ntools; j++)); do seen[j]=0; done
sanitised=0
idx=0
progress=0; [ -t 2 ] && progress=1     # only animate when stderr is a terminal
for d in "${dirs[@]}"; do
  idx=$((idx + 1))
  [ "$progress" -eq 1 ] && \
    printf '\r[without] building shadow PATH... %d/%d\033[K' "$idx" "$total" >&2
  [ -d "$d" ] || continue
  hit=0
  for ((j = 0; j < ntools; j++)); do
    if [ -e "$d/${tools[j]}" ]; then hit=1; seen[j]=1; fi
  done
  if [ "$hit" -eq 0 ]; then
    parts+=("$d")                              # untouched -- nothing to hide here
    continue
  fi
  mir="$farm/d$idx"
  mkdir -p "$mir"
  ln -s "$d"/* "$mir"/ 2>/dev/null || true     # fresh dir => no name clashes
  for ((j = 0; j < ntools; j++)); do rm -f "$mir/${tools[j]}"; done
  parts+=("$mir")
  sanitised=$((sanitised + 1))
done
[ "$progress" -eq 1 ] && printf '\r\033[K' >&2  # wipe the progress line

shadow=$(IFS=:; printf '%s' "${parts[*]}")

# Report what was hidden; warn about names that were never on PATH.
hidden=()
for ((j = 0; j < ntools; j++)); do
  if [ "${seen[j]}" -eq 1 ]; then
    hidden+=("${tools[j]}")
  else
    echo "[without] warning: '${tools[j]}' is not on PATH; nothing to hide." >&2
  fi
done
echo "[without] hidden: ${hidden[*]:-(none)} (${sanitised} dir(s) sanitised) -- exit to restore." >&2

# Generate the rcfile: a dynamic header carrying the values we computed, then a
# static body (quoted heredoc -- nothing expands) that runs the user's normal
# startup and *then* pins PATH and adds the badge on its own line.
label=$(IFS=,; printf '%s' "${hidden[*]:-${tools[*]}}")
{
  printf '_wo_path=%q\n' "$shadow"
  printf '_wo_label=%q\n' "$label"
} > "$rc"
cat >> "$rc" <<'EOF'
[ -f /etc/profile ] && . /etc/profile
[ -f /etc/bash.bashrc ] && . /etc/bash.bashrc
[ -f "$HOME/.bashrc" ] && . "$HOME/.bashrc"
export PATH="$_wo_path"
# Badge on its own line, directly above the prompt.  If PS1 already opens with
# a newline (an actual one or the \n escape), reuse it as the separator so
# there's no blank gap between badge and prompt; otherwise add one.
case $PS1 in
  '\n'* | $'\n'* ) PS1="\n(without:$_wo_label)$PS1" ;;
  *)               PS1="\n(without:$_wo_label)\n$PS1" ;;
esac
unset _wo_path _wo_label
EOF

# Not `exec`: control must return here so the EXIT trap cleans up.
bash --rcfile "$rc" -i
