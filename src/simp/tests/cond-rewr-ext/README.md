# Focused Cond_rewrExt contracts

From the repository root, after the core heap is available:

```
bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache \
  -C src/simp/tests/cond-rewr-ext -j1 check
```

`check` builds **and executes** `selftest.exe`, using `testutils` and the
normal Holmake executable harness. Compiling `.uo` files alone is not a
successful check. No `bin/hol` input pipeline or test-only production hook is
used. The final line reports `Cond_rewrExt focused checks: N`; failures exit
nonzero. The suite imports the real extension explicitly; it must remain a
separate target rather than an import of ordinary `../../src/selftest.sml`.

## Coverage

- Saved legacy and configured runners read the shared
  `Cond_rewr.stack_limit` live for `NONE`; `SOME 0`, `SOME 1` and the integer
  `WITH_CONTEXT` adapter remain fixed. `WITH_CONFIG` forwards explicit depth.
- Multiple conditions prepend in theorem order to the caller's stack. Exact
  depth accounting, loop cuts, matching substitutions, solver arguments,
  retained source and solver hypotheses, and alpha-renamed input are checked.
- Direct ordinary `Cond_rewr.COND_REWR_CONV` is the baseline, never a
  discarded paired projection. Success, miss, self-loop, malformed theorem,
  AC orientation and trace streams are compared with that direct constructor.
- The variable-permutation alias, original AC ordering, custom
  `GREATER`/`LESS`/`EQUAL` orders and instantiated comparison arguments are
  tested. Boolean bounded mode and actual prepared bounded mode bypass AC
  rejection; prepared unbounded mode still enforces orientation.
- `prepare`/`runners` construction and projection are inert. Alternating
  runners, late extraction after partial use and exhaustion, and external
  refill all observe the **actual supplied counter reference**. Each success
  spends exactly once; exhaustion neither calls solvers/order callbacks nor
  makes the counter negative. Unbounded runners remain reusable.
- Failed solvers, invalid solver proofs, misses, depth/loop cuts and reflexive
  rules do not spend a prepared bound. A subsequent successful retry does.
- Private `Callback` and `Fail` solver exceptions are wrapped as `HOL_ERR`
  with `General.exnMessage`, exactly as in the ordinary baseline. Existing
  `HOL_ERR` messages are preserved and their origin chains extended;
  `Portable.Interrupt` itself remains unchanged. Both extension solver runners
  compare exact messages and complete origin chains (or Interrupt identity)
  with the direct ordinary result. Solver exceptions do not spend the bound.
  Custom order callbacks obey the identical contract, checked against
  `Feedback.wrap_exn`: ordinary construction has no arbitrary order callback.
- Malformed rules fail at construction (including both adapters and prepare);
  candidate failures retain application-stage `Cond_rewr` HOL_ERR origins and
  function names. Exhausted prepared bounds fail before entering that engine:
  their exact message and complete origin chain match `liteLib.failwith`
  (`??.failwith`, `Loc_Unknown`, `exceeded rewrite bound`), with no application
  wrapper. Engine callback exceptions use the baseline `STRUCT_WRAP`
  contract, not arbitrary exception propagation.
- Original `Trace` constructors/listener receive exact levels, names, terms,
  proofs and event order for success, solver failure, loop/depth cuts, misses
  and AC rejection. Listener installation is exception-safe and removed after
  each capture. No trace output/timestamps are scraped.
- `Cond_rewr.with_tracking` is the one tracking extent: the extension
  runners report into it through `Cond_rewr.note_rewrite`, so it sees
  ordinary and extension rewrites in the same cell, in firing order. Nested
  extents isolate their lists, exceptional extents restore
  the enclosing accumulator and original exception, and nested candidates
  and failed candidates leave no phantom entries. The outer tracking action's
  private exception retains its original payload identity; it is raised
  outside the conditional engine and is not subject to its wrapper.
- `Cond_rewrExt.is_var_perm` is its own copy of Cond_rewr's unexported
  predicate; permutative rewrites are accepted and refused identically by
  `Cond_rewr.COND_REWR_CONV` and both extension runners.

Every successful rewrite assertion compares both conclusion and hypothesis
set; the fixtures use kernel rules and explicit assumptions, not an oracle.
These are additive tests, not relocations or replacements of existing cases.

The executable establishes observable sharing and construction/application
contracts. This suite does not establish that matcher preparation occurs
**exactly once**: a black-box late-projection test cannot detect rebuilding
an equivalent matcher while preserving its counter.  That ordinary loading
has no extension dependency is checked by `../api-audit`.
