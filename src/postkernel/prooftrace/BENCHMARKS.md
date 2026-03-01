# Proof Trace Benchmarks

## Goal

Measure the overhead of proof tracing on HOL builds, and the
performance of the merge and replay tools.

## Commits

- **Baseline (origin/develop):** `81c9003b5` — TFL: print cheated Modern Syntax termination proofs
- **PR (proof-traces):** `641a2703d` — Add Specialize_thm to otknl

## Target theorems

- `arithmetic.DIVISION`
- `regexp_compiler.regexp_matcher_correct`

Both targets are included in every merge/replay run.

## Preparation

Uninstall pandoc to avoid Docfiles generation overhead.
All commands are below are in the HOL directory.

## Runs

### (a) Baseline build — origin/develop

Fresh full HOL build from the develop branch.

```
git checkout 81c9003b5
git clean -xdf
poly --script tools/smart-configure.sml
/usr/bin/time -v bin/build --nograph &| tee /tmp/bench-a.log
```

### (b) PR build — tracing off

Fresh full HOL build from the PR branch, without `--trace`.

```
git checkout 641a2703d
git clean -xdf
poly --script tools/smart-configure.sml
/usr/bin/time -v bin/build --nograph &| tee /tmp/bench-b.log
```

### (c) PR build — tracing on

Fresh full HOL build from the PR branch, with `--trace`.

```
git clean -xdf
poly --script tools/smart-configure.sml
/usr/bin/time -v bin/build --nograph --trace &| tee /tmp/bench-c.log
```

After the core build, build the regexp_compiler example
(needed for merge/replay targets):

```
cd examples/formal-languages/regular
/usr/bin/time -v ../../../bin/Holmake --trace &| tee /tmp/bench-c-regexp.log
cd -
```

Measure trace file sizes:

```
find . -name "*.pft" -o -name "*.pft.zst" | \
  xargs du -ch | tee /tmp/bench-c-size.log
```

### (d) Merge

Merge traces for both target theorems. Run from the HOL1
root after (c) completes.

```
/usr/bin/time -v bin/prooftrace merge -o bench.pft \
  arithmetic.DIVISION \
  regexp_compiler.regexp_matcher_correct \
  &| tee /tmp/bench-d.log

zstd bench.pft
ls -lh bench.pft bench.pft.zst | tee -a /tmp/bench-d.log
```

### (e) Replay

Replay the merged trace.

```
/usr/bin/time -v bin/prooftrace replay bench.pft \
  &| tee /tmp/bench-e.log
```

## Results

| Run | Description | Wall time | Peak RSS | Notes |
|-----|-------------|-----------|----------|-------|
| (a) | Baseline build | 10m04s | 1.63G   | |
| (b) | PR build, tracing off | 10m08s | 1.41G | |
| (c) | PR build, tracing on | 12m43s | 1.8G | total .pft.zst size: 1.4G |
| (c') | regexp_compiler (tracing on) | 2m46s | 1.48G | |
| (d) | Merge | 4m37s | 15.63G | merged: raw (304M) / zstd (68M) (ratio 4.47) |
| (e) | Replay | 32s | 7.55G | |

**Overhead (b vs a):** kernel changes with tracing off
essentially nothing

**Overhead (c vs b):** tracing I/O and callback cost
noticeable but not excessive

## Hardware

- CPU: 2.30GHz 8-core 11th Gen Intel
- RAM: 32GB DDR4
- Disk: SSD
- OS: GNU/Linux
