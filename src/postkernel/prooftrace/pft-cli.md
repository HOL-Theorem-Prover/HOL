# Converting and merging proof traces

The `pft` driver converts HOL4 proof dumps into version 1 binary PFT files
and merges selected exports from a dependency-ordered set of those files.
It supports the `hol4` and `candle` rulesets. It needs the original proof
dumps; loading a theory without a dump does not reconstruct its proof.

Build the modules from the HOL root before using the driver:

```sh
bin/Holmake -C src/postkernel/prooftrace PFTCLI.uo
```

The driver uses this checkout's `bin/hol run --bare`. Set `PFT_HOL` to
another compatible HOL executable when building with an external toolchain.
Its arguments and file paths may contain spaces. Run it from any directory:

```sh
/path/to/HOL/src/postkernel/prooftrace/pft --help
```

## Convert a theory

Choose the ruleset explicitly for each conversion:

```sh
src/postkernel/prooftrace/pft emit --ruleset hol4 \
  --trace /path/to/exampleTheory.tr.gz --output example.pft
```

For Candle, emit the shared preamble before the converted theories:

```sh
src/postkernel/prooftrace/pft preamble --output preamble.pft
src/postkernel/prooftrace/pft emit --ruleset candle \
  --trace /path/to/exampleTheory.tr.gz --output example.candle.pft
```

Candle proofs using verified computation also need the compute preamble:

```sh
src/postkernel/prooftrace/pft compute-preamble --output compute-preamble.pft
```

Place that file after the converted `cv` dependencies and before theories
that use computation. Each converted theory retains its own explicit
compute-initialization object. The compute preamble supplies shared
computation equations; it does not replace those initialization objects.

## Select and merge exports

Provide input files in dependency order. An order file contains one PFT
path per line, relative to that order file; blank lines are ignored. For
Candle the shared preamble comes first. The merger checks headers before
opening the output and rejects mixed rulesets, unsupported versions,
unresolved theorem references, and references to a later dependency.

```sh
src/postkernel/prooftrace/pft merge --ruleset candle \
  --order traces.order --target 'example$THEOREM' --output selected.pft
```

Repeat `--target` to select more named exports. Use `--all example` for all
named exports of one theory. `--save-defs` also saves the definitions used
by the selected targets. Anonymous cross-theory references (`theory#0`,
for example) resolve through their original SAVE/LOAD names automatically.
Single quotes around `theory$THEOREM` prevent shell variable expansion.

Repeated `--input FILE` arguments supply the order directly. `--order`
expands at its position among those arguments. The merger discards exports
and proof steps unreachable from the selected targets, eliminates
cross-file SAVE/LOAD pairs, and writes a new trace with monotonic IDs and
fresh deletion commands. It preserves the two consecutive results of a
Candle type definition. Input files that reuse an ID after deletion are
rejected; live-ID allocation and compaction are separate work.

## Limits

The raw parser follows the current producer's kernel identifier and proof
constructor layouts, in either TR32 or 64-bit heap encoding. The historical
reference-based kernel identifier layout is rejected. The theory name comes
from the dump's metadata, not its filename.

`Exported` side-file proofs and deleted proofs (including tracing gaps) are
unsupported and fail conversion. No missing proof is replaced by an axiom.
The AXIOM instruction is nevertheless part of both rulesets; callers must
state their axiom policy and check target hypotheses and conclusions. This
command is not a strict certificate-policy checker.

Debug EXPECT records are accepted by Candle but not by the HOL reader or
merger. The CLI emits the supported binary stream without these records.
The portable version-1 format is separate from the producer-specific raw heap
format; changing a raw producer pin requires rechecking its layout.

### Large computation numerals

The tracing regression covers computation results at the cached-translation
boundary and beyond machine integers, through 2^256. It requires a tracing HOL
with `cv_computeLib` and the `exportSmallToFD` Poly/ML support. From an empty
scratch directory containing `.hol/objs`, run:

```sh
/path/to/tracing/bin/hol run \
  /path/to/HOL/src/postkernel/prooftrace/numeral-produce.sml
HOL_PFT_SOURCE_ROOT=/path/to/HOL /path/to/tracing/bin/hol run \
  /path/to/HOL/src/postkernel/prooftrace/numeral-selftest.sml
```

The producer checks each computation's exact equation before export. The
selftest converts the same trace to both rulesets and emits `EXPECT` checks
for Candle replay with its dependency traces. The source directory may differ
from the producer directory, so the same input can test a converter change.

The raw-parser regression is a separate executable:

```sh
bin/Holmake --poly_not_hol -C src/postkernel/prooftrace parser-selftest.exe
```

It uses `PolyML.exportSmall` to generate its inputs and the de Bruijn
kernel layout, so automatic execution requires a tracing-kernel build
with the exportSmall runtime. Stock Poly/ML does not provide that API.
The portable reader/merger suite is `pft-selftest.exe` and continues to run
for every supported kernel and ML implementation.
