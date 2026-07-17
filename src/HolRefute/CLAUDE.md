This file provides guidance to coding agents when working with the HolRefute project code in this repository.

`README` here documents the substrate model and module layout — read it first.

## Build & test

- `Holmake` in this directory builds everything, including `refuteheap` and
  `selftest.exe` (plain `Holmake`, boss-onwards band).  Poly/ML only; the
  tree build skips this directory on other MLs.
- `HOLSELFTESTLEVEL=2 Holmake` also runs the selftest (output tees to
  `holrefute-selftest.log`) and `theory_tests/`.
- After building, `./selftest.exe` reruns the selftest directly;
  `HOLSELFTESTLEVEL=2 ./selftest.exe` enables the level-2 suites
  (cross-substrate conformance, Cv cleanliness, corpus).  `selftest.sml`
  is one program with `diemode := Remember` — there is no finer
  per-test selection.
- Interactive session with all Refute modules loaded:
  `bin/hol --holstate=src/HolRefute/refuteheap`.
- Quality gate: `HOLSELFTESTLEVEL=2 Holmake` here.  Level 2 is not optional —
  cross-substrate conformance, candidate-stream equality, and Cv cleanliness
  only run there.
- The root CLAUDE.md's `--seq=tools/sequences/upto-parallel` pass does not
  reach this directory and adds no signal: it stops before
  `src/parallel_builds`, which is what pulls in HolRefute (POLY-only
  `INCLUDES` in `src/parallel_builds/core/Holmakefile`, sequence
  `more-theories`).  It builds neither HolRefute nor its deps (real, sort,
  n-bit, cv_compute).  Nothing else INCLUDEs HolRefute, so a change confined
  here cannot break upstream; a tree-level check needs `bin/build -F`.

## Architecture

- Pipeline: `Refute_QC` compiles a goal into test-plan IR
  (`Refute_Eval.plan`: `Test`/`Gen`/`Bind`/`Split`/`Guard`/`Prune`); a
  registered substrate (`Refute_Eval.substrate`) compiles plans into a
  `compiled_test` and runs it; `Refute_Cert` certifies candidates.
  `Refute.sml` is a thin facade over `Refute_Core` orchestration.
- Trust model: substrates are untrusted accelerators.  A counterexample
  becomes `Genuine` only after `Refute_Cert` re-evaluates the instantiated
  proposition with computeLib and proves its negation.  No oracle tags.
- Substrate selection: `Auto` falls through inapplicable substrates
  (NativeSML, then Cv, then Compute); an explicitly selected substrate
  never falls through — inapplicability reports `Unknown`.
- Determinism: one 64-bit PRNG (`rand_next`/`rand_out`/`rand_below`,
  defined in refuteTheory, mirrored in SML in `Refute_Eval`,
  cv-translated in `refute_cvScript.sml`).  All substrates must yield the
  identical candidate stream for a given seed; level-2 selftests enforce
  this.  Any change to generation or consumption order must land in all
  three substrates and the theory in lockstep.
- Theory hygiene: Cv performs its per-call definitions and translations
  inside a full theory snapshot/revert bracket.  No Refute-created type,
  constant, theorem, or binding may survive in the user's theory on any
  path (success, failure, timeout, interrupt); if safe cleanup is
  unavailable, report inapplicable instead.  `theory_tests/refuteCvClean*`
  check this.
- Ancestry split: refuteTheory (parents: real, sorting, words) must stay
  cv-free; refute_cvTheory (parents: refute, cv_std) holds the cv
  translations.  The Holmakefile builds `refuteheap` separately to keep
  this split, and the selftest asserts the exact parent sets.

## Testing Guidelines

- Test specified behavior, not implementation internals.
- Bug fixes get a failing-first regression test.
- Tests go in `selftest.sml`: `tprint "name"` then
  `require_msg (check_result f) (fn () => "failure msg") (fn () => ()) ()`.
  `diemode := Remember erc` accumulates failures instead of aborting;
  `exit_count0 erc` turns the count into the exit status.
- Gate by cost on `selftest_level` (reads HOLSELFTESTLEVEL, default 1):
  cheap and targeted ungated; expensive or matrix-shaped behind
  `if selftest_level >= 2`.
- `theory_tests/` only for checks needing a fresh user theory (Cv residue):
  `*Script.sml` descendant theories raising `Fail`, not testutils.  Runs
  under `Holmake` at level >= 2 only, never from `selftest.exe`.
- Don't validate by piping `.sml` into `bin/hol`; the harness only sees
  `selftest.sml`.
- Quality gate: `HOLSELFTESTLEVEL=2 Holmake` in `src/HolRefute/`.
