This file provides guidance to coding agents working with HolRefute in this
repository.

`README` here documents the substrate model and module layout — read it first.

## Build & test

- `Holmake` in this directory builds the module and then recurses into
  `tests/` to build `tests/selftest.exe` (plain `Holmake`, boss-onwards
  band).  Poly/ML only; the tree build skips this directory on other MLs.
- `HOLSELFTESTLEVEL=2 Holmake` also runs the selftest (output tees to
  `tests/holrefute-selftest.log`) and `theory_tests/`.
- After building, `tests/selftest.exe` reruns the selftest directly, from
  inside `tests/` — golden files resolve relative to the cwd.
  `HOLSELFTESTLEVEL=2 ./selftest.exe` there enables the level-2 suites
  (cross-substrate conformance, Cv cleanliness, corpus).
  `tests/selftest.sml` is one program with `diemode := Remember` — there is
  no finer per-test selection.
- `tests/` holds everything test-only: `selftest.sml`, its golden files
  under `tests/goldens/`, and the fixture theories the selftest loads
  (`refuteTableZoo`, `refuteUnused`, `refuteHarvestType`,
  `refuteHarvestAbs`).  It is a child directory with `INCLUDES = ..` and
  `--no_prereqs`, driven by a recursive `Holmake -C`, because a parent may
  not INCLUDE its own subdirectory.  Fixture theories stay out of the
  global sigobj namespace by living here.
- Interactive session: start `bin/hol`, then run `load "Refute"`.
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
  (`Refute_Eval.plan`: `Test`/`Gen`/`Bind`/`Split`/`Guard`/`SmartGuard`/
  `Enum`/`Prune`); a
  registered substrate (`Refute_Eval.substrate`) compiles plans into a
  `compiled_test` and runs it; `Refute_Cert` certifies candidates.
  `Refute.sml` is a thin facade over `Refute_Core` orchestration.
- Trust model: QC certainty comes from the substrate's testing verdict;
  certification is an independent, best-effort theorem audit.  With
  `certify=true` (the default), `Refute_Cert` re-evaluates the instantiated
  proposition with computeLib: proving it true discards the candidate,
  proving it false attaches a theorem, and an inconclusive replay leaves the
  substrate-derived certainty unchanged with `cert = NONE`.  With
  `upd_certify false`, replay is skipped.  Candidates already known to be
  stuck or incomplete during testing remain `Potential` in either mode.  No
  oracle tags.
- `certainty` and `cert` are independent axes: semantic strength vs. "a HOL
  theorem exists".  `Genuine` with `cert = NONE` is valid and expected.
- SETTLED, do not revisit: Refute trusts Kodkodi exactly as Nitpick trusts
  Kodkod, and is never stricter.  Model-finder certainty comes from
  `fallback_certainty` (encoding soundness/exactness), never from whether a
  certificate was built.  Never require a certificate for a `Genuine` model,
  and never "fix" a test expecting `Genuine, cert = NONE` from kodkod.  See
  README; 3948a7bed and 2db19131b did this and were reverted, as was
  92c24de7e, which did it as a budget.  `max_potential` bounds models whose
  *encoding* is unsound, so only liberal problems spend it; every model of a
  sound problem is charged to `max_genuine`.
- Substrate selection: `Auto` falls through inapplicable substrates
  (NativeSML, then Cv, then Compute); an explicitly selected substrate
  never falls through — inapplicability reports `Unknown`.
- SETTLED: backend admission and execution are concurrent by default through
  a worker pool local to each Refute call, even when
  `Multithreading.max_threads () = 1`.  Refute never changes that
  process-global value.  `upd_sequential true` is the complete serial opt-out;
  backend-internal parallelism remains enabled, so oversubscription is an
  intentional possibility.
- One Refute call owns one absolute search deadline.  The default is 10
  seconds, and preprocessing, admission, every backend, native compilation,
  and Kodkodi all consume the same remainder.  Cleanup is mandatory and may
  finish after that deadline; timing itself is never a test verdict.
- Default QC size and MF card bounds are iterative with initial window 10.
  `upd_size` and `upd_card` always select `FixedBound`; only
  `upd_iterative_size` and `upd_iterative_card` restore adaptive mode.  Do not
  turn the 5000-scope materialization batch into a total search limit, and do
  not report adaptive timeout as finite exhaustion.
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
- Ancestry split: refuteTheory (parents: real, sorting, words, rat) must stay
  cv-free; refute_cvTheory (parents: refute, cv_std) holds the cv
  translations.  Their separate `Ancestors` declarations enforce the split,
  and the selftest asserts the exact parent sets.

## Testing Guidelines

- Test specified behavior, not implementation internals.
- Bug fixes get a failing-first regression test.
- Tests go in `tests/selftest.sml`: `tprint "name"` then
  `require_msg (check_result f) (fn () => "failure msg") (fn () => ()) ()`.
  `diemode := Remember erc` accumulates failures instead of aborting;
  `exit_count0 erc` turns the count into the exit status.
- No wall clock in a verdict.  `Timeout.apply` raises only if its timer
  thread beats the body, so "was the deadline reached" is unassertable.
  A spent budget is decided by `Util.apply_within_budget`, degradation
  polarity by `abandoned_mono_verdict`; test those, not the race.
  Three level-2 flakes so far: 8f042b080, 757301f92, and `tac_timeout 0.0`.
- Gate by cost on `selftest_level` (reads HOLSELFTESTLEVEL, default 1):
  cheap and targeted ungated; expensive or matrix-shaped behind
  `if selftest_level >= 2`.
- `theory_tests/` only for checks needing a fresh user theory (Cv residue):
  `*Script.sml` descendant theories raising `Fail`, not testutils.  Runs
  under `Holmake` at level >= 2 only, never from `selftest.exe`.
- Don't validate by piping `.sml` into `bin/hol`; the harness only sees
  `tests/selftest.sml`.
- `examples/` are executable descendant theories showing *typical*
  user-facing usage: conjectures discharged by the four tactics under the
  adaptive defaults, no configuration updaters, no SML-level calls.  Keep
  them that way — pinning `upd_expect`, `upd_card` or `upd_max_threads`
  there stops showing what a user would type.  Example 11 is the sole
  SML-API example and the only one that asserts its own outcomes
  (`upd_expect` plus `raise Fail`).  Deliberately false conjectures are
  admitted by `>> cheat` after the diagnostic has printed.
- Examples are documentation, not regression tests.  `Holmake examples` is
  a manual target, outside `all` and the selftest, and only checks that the
  scripts still run; a changed verdict class shows solely on inspection, so
  reread the prose whenever behavior changes.  Pin behavior in
  `tests/selftest.sml` instead.
- Adaptive scope search makes model-finder output machine-dependent: never
  quote a scope, model or runtime figure in example prose.
  `NoCounterexample` can also come from exhaustive QC or narrowing when a
  finite generator space is completely covered (`examples/README`).
- Quality gate: `HOLSELFTESTLEVEL=2 Holmake` in `src/HolRefute/`.
