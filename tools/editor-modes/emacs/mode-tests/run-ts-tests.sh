#!/bin/sh
# Run the `holscript-ts-mode' ERT test suite in batch Emacs.
#
# Not wired into `bin/build' — see README.md in this directory for the
# rationale.  Run this by hand when touching `holscript-ts-mode.el' or
# the tree-sitter grammar.
#
# Prerequisites: Emacs 29+ with tree-sitter, a C compiler, `make', and
# (if the tree-sitter parser hasn't been built here yet) the
# `tree-sitter' CLI on PATH.

set -eu

script_dir=$(cd "$(dirname "$0")" && pwd)
# script_dir is .../tools/editor-modes/emacs/mode-tests
holdir=$(cd "$script_dir/../../../.." && pwd)
ts_dir="$script_dir/../tree-sitter/tree-sitter-holscript"
lib="$ts_dir/libtree-sitter-holscript.so"

# Build the parser shared object if it's missing.
if ! [ -f "$lib" ]; then
    echo ">>> $lib not found; building..."
    if ! [ -f "$ts_dir/src/parser.c" ]; then
        if ! command -v tree-sitter >/dev/null 2>&1; then
            cat <<EOF >&2
error: tree-sitter CLI is not on PATH and $ts_dir/src/parser.c is missing.
Install the tree-sitter CLI from
  https://github.com/tree-sitter/tree-sitter/releases
and rerun, or generate parser.c yourself and place it in that directory.
EOF
            exit 1
        fi
        (cd "$ts_dir" && tree-sitter generate)
    fi
    (cd "$ts_dir" && make)
fi

exec emacs -batch -l ert \
    --eval "(setenv \"HOLDIR\" \"$holdir/\")" \
    -l "$script_dir/holscript-ts-tests.el" \
    -f ert-run-tests-batch-and-exit
