# Proof Trace Benchmarks

## Goal

Measure the overhead of proof tracing on HOL builds, and the
performance of the merge and replay tools.

## Commits

- **Baseline (origin/develop):** `c38cd4913` — TFL: cleanup auto-delete of support constants
- **PR (proof-traces):** `cc2167173` — Revert deletion of dependencies in proofman/Holmakefile

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
git checkout c38cd4913
git clean -xdf
poly --script tools/smart-configure.sml
/usr/bin/time -v bin/build --nograph &| tee /tmp/bench-a.log
```

### (b) PR build — tracing off

Fresh full HOL build from the PR branch, without `--trace`.

```
git checkout cc2167173
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
| (a) | Baseline build | 10m04s | 1.64G   | |
| (b) | PR build, tracing off | 10m08s | 1.45G | |
| (c) | PR build, tracing on | 13m20s | 2.1G | total .pft.zst size: 1.4G |
| (c') | regexp_compiler (tracing on) | 3m33s | 3.36G | |
| (d) | Merge | 4m29s | 17.44G | merged: raw (292M) / zstd (69M) (ratio 4.23) |
| (e) | Replay | 33s | 7.63G | |

**Overhead (b vs a):** kernel changes with tracing off
essentially nothing

**Overhead (c vs b):** tracing I/O and callback cost
noticeable but not excessive

## Hardware

- CPU: 2.30GHz 8-core 11th Gen Intel
- RAM: 32GB DDR4
- Disk: SSD
- OS: GNU/Linux
