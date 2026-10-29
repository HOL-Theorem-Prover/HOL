# Prooftrace export regressions

Run a fixture with a tracing HOL built using exporter-capable Poly/ML:

```sh
/path/to/HOL/src/postkernel/prooftrace/tests/run.sh oracle \
  /path/to/tracing/bin/hol /scratch/prooftrace
```

The suites are `identity`, `oracle`, `export`, `compute-binder`, and
`term-kind`; `all` runs them together. Sources load from this checkout,
with separate processes for fresh kernel state and logs in the scratch dir.
`compute-binder` also needs `cv_computeLib`.

* `oracle` reproduces hypothesis loss and unsupported HOL `deductAntisym`.
  The HOL checker compares the complete oracle sequent. After Candle replay,
  load `oracle-check-results.ml` and call `check_oracle_results ()` and
  `check_deduct_results ()` for the two exact sequents.
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

The `.ml` checkers run in Candle; their producer programs run in HOL.

## Exported identities

`identity` needs a producer genuinely rebuilt with the export/import hooks;
loading a new `Tracing` structure does not change the instance already used
by `Theory.export_theory`.

It exports deletion, unused replacement, context restoration, private-name
collision and restored-type fixtures. Separate parent and child processes test
imports with different allocation epochs. Seven exact sequents and identity
inventories are checked through raw HOL and separate HOL PFT replay.

Three actual exports must fail explicitly: an unrecorded foreign identity, a
retired foreign identity, and a retained foreign definition whose parent
exported only reflexivity. The last remains unsupported even when the public
constant name can be resolved. Supplemental retired/custom logical-role
fixtures require rejection in raw replay and both conversion modes; they do
not establish complete logical-role replay coverage.
