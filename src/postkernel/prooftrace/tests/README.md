# Prooftrace export regressions

Run a fixture with a tracing HOL built using exporter-capable Poly/ML:

```sh
/path/to/HOL/src/postkernel/prooftrace/tests/run.sh oracle \
  /path/to/tracing/bin/hol /scratch/prooftrace
```

The suites are `identity`, `oracle`, `export`, `compute-binder`, and
`term-kind`, and `mk-abs`; `all` runs them together. Sources load from this
checkout, with separate processes for fresh kernel state and logs in the
scratch dir.
`compute-binder` also needs `cv_computeLib`.

* `oracle` reproduces lost hypotheses. The HOL checker compares the complete
  oracle sequent. After Candle replay, load `oracle-check-results.ml` and
  call `check_oracle_results ()` for the same exact sequent.
* `export` checks specification binders: an unused existential, shadowing,
  and an inner binder named like the introduced constant. Run
  `export-check-candle.ml` after Candle replay to compare all four exports.
* `compute-binder` checks coincident binder names, delayed substitution,
  a numeral beyond machine integer range, and COMB/ABS capture confusion.
  Replay the traced ancestors through `cv` with the logical and compute
  preambles, then run `compute-binder-check.ml` for the four exact sequents.
* `term-kind` checks distinct COMB/ABS nodes with identical children during
  substitution and specification. After replay of `bool` and the fixture,
  run `term-kind-check.ml` in Candle, or call `term_kind_check db` from
  `term-kind-check.sml` in a minimal HOL session.
* `mk-abs` reproduces a clashing cosmetic abstraction binder whose converted
  name differs from the raw proof's opened binder. It checks the exact sequent
  through the unchanged HOL4 `Mk_abs` replay handler in a fresh minimal heap.

The `.ml` checkers run in Candle; their producer programs run in HOL.

## Exported identities

`identity` needs a producer genuinely rebuilt with the export/import hooks;
loading a new `Tracing` structure does not change the instance already used
by `Theory.export_theory`.

The two actual exports reproduce a restored constant being replayed as its
retired replacement and a generated private name colliding with a live
constant. The checker compares the exact exported sequents and symbol names
through raw HOL and separate HOL PFT replay.
