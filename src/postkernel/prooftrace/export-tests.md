# Export regressions

These tests export real tracing-kernel proofs before converting them. They
require an exporter-capable Poly/ML runtime and a built tracing HOL. Run them
in scratch directories containing `.hol/objs`; `HOL_PFT_SOURCE_ROOT` selects
the converter checkout independently of the producer.

## Oracle hypotheses

```sh
HOL_PFT_SOURCE_ROOT=/path/to/HOL /path/to/tracing/bin/hol run \
  /path/to/HOL/src/postkernel/prooftrace/oracle-selftest.sml
```

This checks five exact oracle sequents through separate and merged HOL
replay: empty, one, two, overlapping and duplicate hypotheses. The deliberately
tagged test oracles are not axiom-free proofs. Conversion represents each
oracle obligation as a conditional AXIOM, then restores its hypotheses with
checked inference steps.

The producer also exports three `deductAntisym` cases. HOL conversion must
report its explicit unsupported error; Candle supports these cases. For
Candle replay, convert both exported theories with the Candle preamble,
then load `oracle-check-results.ml`. It independently checks all eight
hypothesis sets and conclusions with `check_oracle_results ()` and
`check_deduct_results ()`.

## Specifications

For each `CASE` in `vacuous`, `shadow`, and `overlap`, run in a separate
scratch directory:

```sh
HOL_PFT_EXPORT_CASE="$CASE" /path/to/tracing/bin/hol run \
  /path/to/HOL/src/postkernel/prooftrace/export-produce.sml
HOL_PFT_EXPORT_CASE="$CASE" HOL_PFT_SOURCE_ROOT=/path/to/HOL \
  /path/to/tracing/bin/hol run \
  /path/to/HOL/src/postkernel/prooftrace/export-selftest.sml
```

The fixtures introduce four test constants. They check the exact source
sequents for an unused existential, a shadowed existential variable, and
an inner binder named like the introduced constant. A later reflexivity
proof also uses the constant introduced by the unused existential.

Convert their traced ancestors in dependency order, after the Candle
preamble. Select `pftExport_shadow$SHADOW`, `pftExport_overlap$OVERLAP`,
`pftExport_vacuous$VACUOUS`, and `pftExport_vacuous$UNUSED_REFL` when merging.
After separate or merged Candle replay, load `export-check-candle.ml`.
It checks the four exact conclusions and requires empty hypothesis sets,
then prints `EXPORTS_REPLAYED_EXACT`.
