# HOL4 — quick notes for AI assistants

Long-form developer documentation lives under `Manual/Developers/`
and `developers/`.  This file is the always-loaded "things to
remember before you touch anything" tier.

## Branching

Branch new work off `origin/develop`, not local HEAD or arbitrary
tags.  PRs target `develop`.

## Building

Fresh checkout: `poly < tools/smart-configure.sml`.

Routine sanity check after edits to compiled sources:

    bin/build -t --seq=tools/sequences/upto-parallel

builds up to `src/parallel_builds/` — the practical "kernel +
libraries still healthy?" pass.  `bin/build -F` does the full build;
`-t` enables selftests.  Use `-F` explicitly: bare `bin/build` reuses
the previous invocation's `--seq=…` (whatever partial sequence you
ran last), which can silently skip whole swaths of the tree.

For per-directory `Holmake` invocations, the build sequence divides
directories into three bands by heap selection.  Plain `Holmake`
suffices from `src/boss` onwards; earlier directories need
`--holstate=<repo-root>/bin/hol.state0`; and the very earliest
(`src/portableML` through `src/1`) need `--poly_not_hol`.

## Testing

Tests for code in a directory live in that directory's `selftest.sml`,
using the helpers in `testutils` (`tprint` + `OK`/`die`, `test`,
`convtest`).  Don't validate changes by piping `.sml` into `bin/hol`;
the regression harness goes through `selftest.sml`.

## Style

  - No TAB characters in source files.
  - No trailing whitespace.
  - Strongly prefer < 80 columns.

`tools/h4pedant` enforces tabs/whitespace as part of the
regression suite.

## Inside a sandboxed Linux VM

If you're a Claude session running inside an OrbStack VM that mounts
the repo as `/repo`, see `developers/claude/LOCKED-VM.md` for the
network/permissions model and the worktree workflow.
