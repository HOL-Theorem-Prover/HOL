# Prooftrace export regressions

Run all genuine-export fixtures, or select one suite:

```sh
/path/to/HOL/src/postkernel/prooftrace/tests/run.sh all \
  /path/to/tracing/bin/hol /scratch/prooftrace
```

The suites are `identity`, `oracle`, `export`, `numeral`, `compute-binder`,
and `term-kind`. Each gets its own scratch subdirectory and per-phase logs.
The runner requires a built tracing HOL with exporter-capable Poly/ML;
`numeral` and `compute-binder` also need `cv_computeLib`. It loads converter
sources from this checkout, so the producer and converter can differ.

The compiled parser and portable reader/merger selftests remain in the parent
directory and run through Holmake. The fixtures here need separate processes
for fresh kernel state; Candle checkers must run in the Candle runtime.

## Oracle hypotheses

`oracle` checks five exact sequents through separate and merged HOL replay:
empty, one, two, overlapping and duplicate hypotheses. The deliberately tagged
oracles are not axiom-free proofs. Conversion represents each obligation as a
conditional AXIOM, then restores its hypotheses with checked inference steps.

It also exports three `deductAntisym` cases and requires HOL conversion to
reject them explicitly. Candle supports these cases: convert both exported
theories with the Candle preamble, then load `oracle-check-results.ml` and call
`check_oracle_results ()` and `check_deduct_results ()`. These check all eight
hypothesis sets and conclusions.

## Compute and numerals

`compute-binder` exports ten kernel compute theorems: simple and nested LETs,
coincident binder names requiring capture avoidance, delayed substitutions,
and numerals 255, 256, 257 and 18446744073709551616. It checks native results
exactly and requires raw closures in the delayed-substitution traces, all ten
converted compute steps, and a fresh capture-safe binder.

Two further term-kind cases use well-typed COMB and ABS nodes with identical
children. They check SUBST through the abstraction and prevent its bound
variable from being counted free during closure capture analysis.

For Candle, convert the traced ancestors through `cv`, loading the Candle
preamble first and compute preamble immediately after `cv`. For merged replay,
select all exports from `pft_compute_binders`. After either replay mode, load
`compute-binder-check.ml`: it requires all twelve exact conclusions and empty
hypothesis sets, printing `COMPUTE_BINDER_ALL_EXACT_PASS`.

`numeral` separately checks arithmetic results through 2^256, converts to both
rulesets, and emits EXPECT records for Candle replay with dependency traces.

## Specifications

`export` runs three fresh processes for `vacuous`, `shadow`, and `overlap`.
The fixtures introduce four constants and check exact source sequents for an
unused existential, a shadowed existential variable, and an inner binder named
like the introduced constant. A later reflexivity proof uses the constant
introduced by the unused existential. Each trace is converted to both rulesets.

For Candle, convert ancestors in dependency order after the preamble. Select
`pftExport_shadow$SHADOW`, `pftExport_overlap$OVERLAP`,
`pftExport_vacuous$VACUOUS`, and `pftExport_vacuous$UNUSED_REFL` when merging.
After either replay mode, load `export-check-candle.ml`: it requires the four
exact conclusions and empty hypothesis sets, printing `EXPORTS_REPLAYED_EXACT`.

## Exported identities

`identity` needs a producer genuinely rebuilt with the export/import hooks;
loading a new `Tracing` structure does not change the instance already used
by `Theory.export_theory`.

It exports deletion, unused replacement, context restoration, private-name
collision and restored-type fixtures. Separate parent and child processes test
imports with different allocation epochs. Seven exact sequents and identity
inventories are checked through raw HOL and separate/merged HOL PFT replay.
The merger may omit unused public declarations.

Three actual exports must fail explicitly: an unrecorded foreign identity, a
retired foreign identity, and a retained foreign definition whose parent
exported only reflexivity. The last remains unsupported even when the public
constant name can be resolved. Supplemental retired/custom logical-role
fixtures require rejection in raw replay and both conversion modes; they do
not establish complete logical-role replay coverage.

## Term kinds

`term-kind` exports `pft_term_kinds`, checks native sequents and raw SUBST/spec
constructors, and converts to both rulesets. Both cases retain a COMB proof
whose child pair also belongs to an ABS. One substitutes under coincident
nested binders; the other introduces an unused constant from a vacuous
existential.

For Candle, replay the preamble and `bool`, then the fixture and
`term-kind-check.ml`. For HOL, use the minimal heap, replay `bool` and the
fixture, load `term-kind-check.sml`, and call `term_kind_check db`. For merged
checks select all of `pft_term_kinds`. Both checkers require two exact
conclusions, empty hypotheses and the unused constant; they print
`TERM_KIND_CANDLE_ALL_EXACT_PASS` or `TERM_KIND_HOL_ALL_EXACT_PASS`.
