# Prooftrace export regressions

Run a fixture with a tracing HOL built using exporter-capable Poly/ML:

```sh
/path/to/HOL/src/postkernel/prooftrace/tests/run.sh oracle \
  /path/to/tracing/bin/hol /scratch/prooftrace
```

The suites are `identity`, `oracle`, `export`, `compute-binder`,
`term-kind`, `mk-abs`, and `closedness`; `all` runs them together. Sources
load from this checkout, with separate processes for fresh kernel state and
logs in the scratch dir.
`compute-binder` also needs `cv_computeLib`.

* `closedness` reproduces the closedness sentinel collision for a closed
  abstraction containing another closed abstraction. It also checks that an
  unvisited term retains its sentinel.
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
  substitution and specification, and empty-named binder capture. After replay
  of `bool` and the fixture,
  run `term-kind-check.ml` in Candle, or call `term_kind_check db` from
  `term-kind-check.sml` in a minimal HOL session.
* `mk-abs` reproduces a clashing cosmetic abstraction binder whose converted
  name differs from the raw proof's opened binder. It checks the exact sequent
  in a fresh minimal heap. The converter emits `ABS` and `TRANS` for the
  mismatch; matching binders still use `Mk_abs`. The test also checks those
  instructions, so the replayer's compatibility repair cannot hide a failure.

The `.ml` checkers run in Candle; their producer programs run in HOL.

## Exported identities

`identity` needs a producer genuinely rebuilt with the export/import hooks;
loading a new `Tracing` structure does not change the instance already used
by `Theory.export_theory`.

The identity suite retains the raw producer/loader regressions and also
converts their outputs. It compares all seven exact exported sequents and
required public/private names through raw HOL and separate HOL PFT replay.
It also converts an already-negated `NOT_INTRO` premise to Candle. Replay
`bool` and `identity_negation.candle.pft` after the logical preamble, then
run `identity-check-candle.ml` to check that theorem's exact sequent.
