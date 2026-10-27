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

The producer must have `cv_computeLib` available. The runner genuinely exports ten kernel compute theorems and two term-kind
regressions into `compute-binders.pft.bin`. Compute cases cover a simple LET,
nested LETs using both bound variables, coincident binder names requiring
capture avoidance, delayed substitutions, and numerals 255, 256, 257 and
18446744073709551616. It checks native compute results exactly and verifies
that the delayed-substitution cases retain raw closures in the exported trace.
The converted file must contain all ten compute steps and a fresh capture-safe
binder.

The term-kind cases use well-typed COMB and ABS nodes with identical children.
They check SUBST through the abstraction and prevent its bound variable from
being counted free during closure capture analysis.

For Candle replay, convert the traced ancestors through `cv` and load them
with the Candle preamble first and compute preamble immediately after `cv`. For merged
replay, select all exported theorems in `pft_compute_binders`. After either
separate or merged replay, load `compute-binder-check.ml`. It requires all
twelve exact conclusions and empty hypothesis sets, then prints
`COMPUTE_BINDER_ALL_EXACT_PASS`.

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

## Term kind discrimination

```sh
/path/to/HOL/src/postkernel/prooftrace/term-kind-tests.sh \
  /path/to/tracing/bin/hol /scratch/term-kind
```

This runner genuinely exports `pft_term_kinds`, checks its native sequents and
raw SUBST/specification proof constructors, then writes
`term-kinds.candle.pft.bin` and `term-kinds.hol4.pft.bin`. Both cases retain a
COMB proof whose child pair also belongs to an ABS. One exercises substitution
under coincident nested binders; the other uses the existing specification
primitive to introduce an unused test constant from a vacuous existential.

For Candle, replay the preamble and `bool` before this file, then load
`term-kind-check.ml`. For HOL, replay `bool` and this file using the minimal
heap, load `term-kind-check.sml`, and call `term_kind_check db` with the replay
database. For either merged check, select all of `pft_term_kinds`. Both
checkers require the two exact conclusions, empty hypothesis sets, and the
declared unused constant. They print `TERM_KIND_CANDLE_ALL_EXACT_PASS` or
`TERM_KIND_HOL_ALL_EXACT_PASS`.
