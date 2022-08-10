#!/usr/bin/env bash
# Wraps an interactive hol session and $EDITOR (of vim flavour) side-by-side in
# a tmux session. HOL and $EDITOR are connected by a fresh VIMHOL_FIFO pipe,
# which is erased when quitting the tmux session. Any given argument files are
# opened in the $EDITOR. The working directory of HOL is set to the first
# argument file's, and defaults to the current working directory.
#
# usage:
#     ./vimhol.sh [files...]
#
# It should not be necessary to set the $HOLDIR environment variable as this
# script is ensured to work even when sym-linked, for example by
#     ln -s $HOLDIR/tools/vim/vimhol.sh /usr/local/bin/vimhol
#

# locate HOLDIR
if test -x "$HOLDIR/bin/hol" \
  -a -f "$HOLDIR/tools/vim/hol-config.sml" \
  -a -f "$HOLDIR/tools/vim/filetype.vim"; then
  VIMOPT="$HOLDIR/tools/vim/filetype.vim"
else
  # follow symlink of this script's location
  # https://stackoverflow.com/questions/59895/
  SOURCE="${BASH_SOURCE[0]}"
  # resolve $SOURCE until the file is no longer a symlink
  while [ -h "$SOURCE" ]; do
    DIR="$( cd -P "$( dirname "$SOURCE" )" >/dev/null 2>&1 && pwd )"
    SOURCE="$(readlink "$SOURCE")"
    # if $SOURCE was a relative symlink, we need to resolve it
    # relative to the path where the symlink file was located
    [[ $SOURCE != /* ]] && SOURCE="$DIR/$SOURCE"
  done
  VIMHOLDIR="$( cd -P "$( dirname "$SOURCE" )" >/dev/null 2>&1 && pwd )"
  if test -x "$VIMHOLDIR/../../bin/hol" \
    -a -f "$VIMHOLDIR/hol-config.sml" \
    -a -f "$VIMHOLDIR/filetype.vim"; then
    VIMOPT="$VIMHOLDIR/filetype.vim"
    HOLDIR="$(cd "$VIMHOLDIR/../.." && pwd)"
  else
    echo "Failed to locate the files"
    echo "\$HOLDIR/bin/hol"
    echo "\$HOLDIR/tools/vim/filetype.vim"
    echo "\$HOLDIR/tools/vim/hol-config.sml"
    echo "with HOLDIR=\"$HOLDIR\"."
    echo "Set the \$HOLDIR environment variable to point to the root directory"
    echo "of the HOL installation (e.g. in .bash_profile)."
    exit
  fi
fi

# find rlwrap if installed
RLWRAP="$(command -v rlwrap 2> /dev/null)" || RLWRAP=""

# get absolute pathnames of the argument files, because the working directory
# is later changed
cwd="$(pwd)"
files=()
for f in "$@"; do
  test "${f:0:1}" = "/" || f="${cwd}/$f"
  files+=("$f")
done

# first argument's directory or current working directory
WD="$(echo "$@" | xargs dirname 2>/dev/null \
      | cat - <(pwd) | head -n 1)"

# create new fifo pipe
VIMHOL_FIFO="$(env TMPDIR="${XDG_RUNTIME_DIR:-/tmp}" mktemp -t "hol-XXXXXXXXXX")"
test -p "$VIMHOL_FIFO" || mkfifo "$VIMHOL_FIFO"

# For $HOLDIR/bin/hol, set $HOL_CONFIG to use $HOLDIR/tools/vim/hol-config.sml
# Early tmux versions neither support hooks (to delete VIMHOL_FIFO) nor the -c
# flag (to set the cwd).
tmux \
  new-session \
    -s "$(basename "$VIMHOL_FIFO")" \
    "env VIMHOL_FIFO='$VIMHOL_FIFO' ${EDITOR:-vim} -c 'source $VIMOPT' \
        -c 'bufdo doautocmd BufRead' $*" \; \
  split-window -h "cd '$WD'; env HOL_CONFIG='$HOLDIR/tools/vim/hol-config.sml' VIMHOL_FIFO='$VIMHOL_FIFO' $RLWRAP $HOLDIR/bin/hol" \; \
  select-pane -t :.- \; \
  bind-key C-q confirm-before -p "kill-session #S? (y/n)" \
    "run-shell 'rm -f $VIMHOL_FIFO'; kill-session" \; \
  run-shell "tmux set-hook -t '#S' -g session-closed 'run-shell \"rm -f $VIMHOL_FIFO\"'" \; \
  set-option status off

