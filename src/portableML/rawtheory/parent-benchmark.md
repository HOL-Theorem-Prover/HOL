# Theory.dat parent-reader benchmark

`parent-benchmark-load.ML` loads a standalone, source-only Poly/ML harness.
It does not build an executable or write theory artifacts. Run it from
`src/portableML/rawtheory` in an already configured/built HOL checkout.
Loading uses the existing `mkdatprinter.ML` setup; startup is not timed.

## Example

Start `poly` in this directory and enter:

```sml
val root = OS.FileSys.fullPath "../../..";
use "parent-benchmark-load.ML";

(* Benchmark policy only: use this installation's sigobj links.
   TheoryDat itself contains no artifact-search policy. *)
fun resolve thy =
    let
      val uo = OS.Path.concat
                 (OS.Path.concat (root, "sigobj"), thy ^ "Theory.uo")
      val dir = OS.Path.dir (OS.FileSys.realPath uo)
      val dat = OS.Path.concat (dir, thy ^ "Theory.dat")
    in TheoryDat.Artifact dat end
    handle OS.SysErr _ => TheoryDat.Missing;

ParentBenchmark.run {
  paths = [OS.Path.concat (root, "src/bool/.hol/objs/boolTheory.dat")],
  resolve = resolve,
  iterations = 100,
  rounds = 5
};
```

Replace `paths` with a representative sample. Find candidate sizes without
reading every complete file:

```sh
find src -name '*Theory.dat' -printf '%s %p\n' | sort -n
```

Include bool (bootstrap parent), small and medium theories, and several of
the largest products from different libraries. Benchmark each cached
installation under `~/.cache/holbuild/hol-toolchains/*/hol` separately:
use its absolute root and its artifacts for resolution, not the current
checkout's parents. Do not combine incompatible installations' artifacts.
The resolver must resolve every recorded non-bootstrap parent; a missing
parent aborts the benchmark rather than timing unsuccessful validation.

## What it measures

Before timing each file the harness checks that all three readers return
identical parent identities and that complete parent validation succeeds.
The old scanner is the pre-change Holmake implementation, retained in the
harness. The structured baseline uses the same parser and decoder as
`RawTheoryReader.load_raw_thydata`, but reads through a stream to avoid
HOLFileSys munging of the supplied physical `.hol/objs` paths.

Each round rotates the order of five measurements:

- `old`: full-file textual Holmake scanner;
- `header`: new streaming parent-header reader;
- `full`: complete structured raw-theory parsing/decoding;
- `parent-sha1`: SHA1 of every non-bootstrap parent artifact;
- `validation`: new header reader, resolver, and parent SHA1 comparisons.

All are repeated-read measurements with warm filesystem caches. Each
measurement starts with a full GC outside its timed interval. CSV rows
report total wall, user CPU, system CPU, and GC seconds for the specified
iteration count. Divide wall time by iterations for per-check cost. GC time
is diagnostic, not a separate time to add to wall time. Allocation volume
is not measured. There is no parent-hash memoization in this harness.

Choose iterations so the fastest measurements last long enough to exceed
timer noise; use fewer iterations for very large files if necessary. Use
several rounds and report medians and ranges, not just the fastest result.
Keep the machine otherwise idle. Record HOL revision, Poly/ML version,
architecture, sample sizes, iteration counts, and raw output with the PR.

The key question is reader overhead relative to the old scanner. The
separate SHA1 and validation measurements show whether parent hashing,
resolver work, or header parsing dominates actual cache-check cost.
This is not a cold-disk benchmark or an end-to-end Holmake benchmark.
