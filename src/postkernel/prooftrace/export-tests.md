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

## Compute binders

```sh
/path/to/HOL/src/postkernel/prooftrace/compute-binder-tests.sh \
  /path/to/tracing/bin/hol /scratch/compute-binder
```

The runner genuinely exports three kernel compute theorems and two term-kind
regressions, then converts them
into `compute-binders.pft.bin`. It checks a simple LET, nested LETs using both
bound variables, and coincident binder names requiring capture avoidance.
Native results are checked exactly, and the converted file must contain all
three compute steps and a fresh capture-safe binder.

The term-kind cases use well-typed COMB and ABS nodes with identical children.
They check SUBST through the abstraction and prevent its bound variable from
being counted free during closure capture analysis.

For Candle replay, convert the traced ancestors through `cv` and load them
with the Candle preamble and compute preamble before this file. For merged
replay, select all exported theorems in `pft_compute_binders`. After either
separate or merged replay, load `compute-binder-check.ml`. It requires the exact
five conclusions and empty
hypothesis sets, then prints `COMPUTE_BINDER_ALL_EXACT_PASS`.

These cases cover bound indices under ordinary COMB/ABS nodes. They do not
establish numeral translation through every delayed-substitution form.

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

## Exported identities

```sh
/path/to/HOL/src/postkernel/prooftrace/identity-tests.sh \
  /path/to/tracing/bin/hol /scratch/identity
```

The producer must be genuinely rebuilt with the export/import hooks; loading
another `Tracing` structure into an existing heap does not change the instance
used by `Theory.export_theory`.

The runner exports deletion, unused replacement, context restoration,
private-name collision and restored-type fixtures through `export_theory`.
Separate parent and child processes test imports with different allocation
epochs. It checks seven exact sequents and private/public identity inventories
through raw HOL and separate/merged HOL PFT replay. The merged case may omit
unused public declarations.

Three additional actual exports must fail explicitly: an unrecorded foreign
identity, a retired foreign identity, and a retained foreign definition whose
parent exported only reflexivity. The latter remains unsupported even when
its public constant name can be resolved.

The retired and custom logical-role tests are supplemental low-level tracing
fixtures, not successful theory-export tests. They require explicit rejection
in raw replay and both portable conversion modes. Noncanonical logical roles
and nonconstant implicit-role shapes remain unsupported; the tests do not
establish complete logical-role replay coverage.
