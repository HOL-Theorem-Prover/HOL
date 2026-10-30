# Converting proof traces

The `pft` driver converts HOL4 proof dumps into version 1 binary PFT files.
It supports the `hol4` and `candle` rulesets. It needs the original proof
dumps; loading a theory without a dump does not reconstruct its proof.

Regenerate raw traces with the identity-aware producer. Its export-time
signature determines which identities retain public names. Retired local
identities receive distinct private names, avoiding collisions with live
declarations. Imported public identities are recognized from recorded origin
metadata rather than their process-local epochs. Portable PFT remains version 1.

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

## Limits

The raw parser follows the current producer's kernel identifier and proof
constructor layouts, in either TR32 or 64-bit heap encoding. The historical
reference-based kernel identifier layout is rejected. The theory name comes
from the dump's metadata, not its filename.

HOL4 conversion rejects `deductAntisym`: the portable HOL replayer lacks
that rule. Candle conversion supports it.

Retired imported identities, retired or noncanonical registered logical
roles, and unsupported foreign-definition proofs are rejected explicitly. Naming an
identity does not recover a missing defining proof or reproduce a retired
logical registration; this converter does not yet cover all such exports.

`Exported` side-file proofs and deleted proofs (including tracing gaps) are
unsupported and fail conversion. No missing proof is replaced by an axiom.
The AXIOM instruction is nevertheless part of both rulesets; callers must
state their axiom policy and check target hypotheses and conclusions. This
command is not a strict certificate-policy checker.

For an oracle with hypotheses, conversion asserts the corresponding
conditional proposition and restores the hypotheses with checked inference
steps. It does not assert the conclusion unconditionally. Axiom policies
must account for these conditional oracle obligations.

Debug EXPECT records are accepted by Candle but not by the HOL reader. The CLI emits the supported binary stream without these records.
The portable version-1 format is separate from the producer-specific raw heap
format; changing a raw producer pin requires rechecking its layout.

### Regression tests

The [export regressions](tests/README.md) cover oracle hypotheses, binder
capture, term kinds, identity restoration/collisions and large computation numerals.
Run them with an exporter-capable tracing HOL:

```sh
src/postkernel/prooftrace/tests/run.sh all /path/to/tracing/bin/hol /scratch/pft
```

The raw-parser regression is a separate executable:

```sh
bin/Holmake --poly_not_hol -C src/postkernel/prooftrace parser-selftest.exe
```

It uses `PolyML.exportSmall` to generate its inputs and the de Bruijn
kernel layout, so automatic execution requires a tracing-kernel build
with the exportSmall runtime. Stock Poly/ML does not provide that API.
