# Focused TraverseExt contracts

Run from the repository root, with the core heap:

```
bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache \
  -C src/simp/tests/traverse-ext -j1 check
```

`check` builds **and executes** `selftest.exe`. No `bin/hol` input
pipelines or mixed simpset adapters are used. `selftest.sml` instantiates
its signature-parameterized test body with the actual `TraverseExt`
structure.

Coverage:

- Explicit ordinary lifting, inert lifting/record views, explicit collector
  counts, context exception payload identity, solver/conv/stack/relation/refl
  forwarding, native integer/option record adapters.
- All three reducer constructors: saved TRAVERSE construction-once versus
  per-application XTRAVERSE, explicit-context, root and observer entry points;
  collector/fact ordering, empty context and reuse.
- NONE reaches each native candidate inside one reducer's FIRST_CONV, even
  after an earlier candidate changes the shared `Cond_rewr.stack_limit`;
  SOME zero/one stay explicit, saved NONE stays live, CONTEXT samples at its
  callback, and custom order controls a native permutative rewrite.
- Generic subgoaler/solver fact and stack order, recursive prepend versus
  solver-only append, separation from reducer collection, and capture-safe
  binder traversal without a generic solver provider.
- One-step root rewriting with no child descent, full recursive proving of
  root side conditions, parent/child-first visitation and overlap proofs.
- Eta head preservation, selected abstraction retention, logical-binder
  exclusions, abstraction-body normalization and exact normalization charges.
- Failed side-condition observation with exact observer/reducer/solver/charge
  counts; observer and charge HOL_ERR, foreign payload and Interrupt identity,
  including callback errors passing through conditional-rewrite wrappers.
- Default eager factory schedules compared with ordinary traversal for high,
  low and aborting reducers; reuse, lazy extended/root factories, rejected
  factories, initial collector exception stages, shared Trace listener.
- Failed recursive proofs restore traversal limits, preserve exact callback
  order, and transport rewritten-condition proofs through ordered solvers.

The lifetime/collector/default/factory observations derive from
`../contracts/TraversalContracts.sml`; extension assertions also correspond
to the mixed `../../src/selftest.sml` extended-traversal block, R2 lifetime
and P1 generic-context contracts. These are additive tests: no existing
contract body, ordinary test, or source is replaced. This suite uses none of
the mixed legacy constructors.

Successful execution prints `TraverseExt focused checks: 129` and exits zero.
The counter includes `convtest` assertions. Reducers crossing the boundary
in either direction are rejected statically; see `../type-boundaries`.
The parent `../../src/Holmakefile` runs this separate target at selftest level 1;
ordinary `selftest.sml` does not import the new engine.
