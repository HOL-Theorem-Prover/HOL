# Ordinary/extension engine isolation and sharing

This fixture owns no production code. It uses `testutils` with fail-fast
executable launchers, not SML piped into `hol`.

From the repository root:

```sh
bin/Holmake -C src/simp/tests/api-audit check
```

`check` compiles `Documentation.sml` against the real signatures but
**does not link it into the launcher**. It then runs `selftest.exe` in
eight fresh processes: `simpLib` then `congLib`, or the reverse, each with a
foreign split attribute or exporter owner installed before or after the
ordinary imports. Exporters install their own attribute dispatcher, so the
two foreign owners are tested in separate processes, not registered over
each other.

## Executed contracts

- Entry, each ordinary import and ordinary recipes check loaded modules,
  global structure bindings, actual used files and the loader's file map.
  Extension modules and private splitter/marker modules are forbidden.
  Actual requested, used and loaded paths are printed separately; this is
  not a dependency-name-only scan.
- Exporter record pointers, the attribute's presence, foreign theorem data
  and callback behavior survive ordinary and explicit extension imports.
  Imports/proofs invoke no foreign attribute/exporter initialization
  callbacks. Existing Theory listener function pointers/order are retained;
  ordinary additions must be the exact legacy list. Extension imports/use
  add no listeners and never initialize split persistence.
- Original `Cond_rewr.stack_limit`, `Trace.trace_hook` and the registered
  `simplifier` traces are captured before extension import. Saved ordinary
  and extension conversions see live shared depth changes; explicit
  extension depths are local. Proofs compare complete conclusions and
  hypotheses.
- `HOLFlags`' `simplifier.trace` is the one simplifier trace level, and the
  extension registers no other. One original Trace listener observes actual
  rewrites by both engines. Nested tracking in both directions, exceptional
  restoration and empty-scope cleanup use real kernel rewrite proofs.
- Two **single-sided** names test independent fragment registries. Opposite
  lookup is absent and opposite SF tactic consumption must raise the specific
  missing-fragment error. Own-registry tactics work; failures do not populate
  the other registry. Context is restored afterwards.
- `Documentation.sml` gives typed tracked construction, both traversal
  projections, explicit one-way ordinary reducer/public congruence-fragment
  lifts, prepared bundles and source views. Its executable examples prove
  the lifts work and that bundle/view aliases share remaining/exhausted
  actual controls. No opaque simpset or congset promotion is offered.
