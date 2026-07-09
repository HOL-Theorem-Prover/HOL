# Emacs mode tests

ERT tests for the two Emacs modes that ship with HOL:

- `holscript-mode` — SMIE-based, older.  Tests in `holscript-tests.el`.
- `holscript-ts-mode` — tree-sitter based, newer.  Tests in
  `holscript-ts-tests.el`.

**Neither suite is wired into `bin/build`.**  They require Emacs 29+
(with tree-sitter support for the ts-mode suite) and a compiled parser
library; asking every HOL user to install those just to `bin/build -t`
is heavier than the tests' value warrants.  Run them by hand when
touching the mode files or the tree-sitter grammar.

## Running the tree-sitter mode suite

    ./run-ts-tests.sh

Prerequisites the script assumes:

- **Emacs 29+** with tree-sitter support (`M-: (treesit-available-p)`
  should return `t` in your Emacs).
- **A C compiler** and **make** — needed to build the parser shared
  library if it isn't already present at
  `../tree-sitter/tree-sitter-holscript/libtree-sitter-holscript.so`.
- **The `tree-sitter` CLI** on `PATH`, if
  `../tree-sitter/tree-sitter-holscript/src/parser.c` also isn't
  present (the generated file is `.gitignore`d).  Install from
  <https://github.com/tree-sitter/tree-sitter/releases>.

The script builds the parser if needed, then runs

    HOLDIR=<repo-root>/ emacs -batch -l ert \
        -l holscript-ts-tests.el -f ert-run-tests-batch-and-exit

and exits non-zero if any test fails.  Expected output ends with a
line like `Ran 27 tests, 27 results as expected`.

## Running the SMIE mode suite

The SMIE mode is plain elisp — no parser to build:

    HOLDIR=$(git rev-parse --show-toplevel)/ \
        emacs -batch -l ert \
        -l tools/editor-modes/emacs/mode-tests/holscript-tests.el \
        -f ert-run-tests-batch-and-exit

## Adding tests

Add new `ert-deftest` forms to `holscript-ts-tests.el` (or
`holscript-tests.el` for the SMIE mode).

For scenarios that fit in a small self-contained snippet, use the
inline-content helper defined near the bottom of
`holscript-ts-tests.el`:

    (holscript-ts-tests--with-string CONTENT
      BODY...)

`CONTENT` is a string inserted into a fresh `holscript-ts-mode`
buffer.  Then `holscript-ts-tests--indent-after-strip REGEX` finds the
first line matching REGEX, strips its leading whitespace, hits TAB,
and returns the resulting column — most of the indent tests use that
pattern.

For scenarios that need real-world context, add a small
`*Script.sml` fixture next to `sampleScript.sml` / `indentScript.sml`
and use `holscript-ts-tests--fixture` to load it.
