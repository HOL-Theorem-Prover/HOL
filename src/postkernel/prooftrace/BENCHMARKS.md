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
| (a) | Baseline build | | | |
| (b) | PR build, tracing off | | | |
| (c) | PR build, tracing on | | | total .pft size: |
| (c') | regexp_compiler (tracing on) | | | |
| (d) | Merge | | | merged: raw / zstd (ratio) |
| (e) | Replay | | | |

**Overhead (b vs a):** kernel changes with tracing off
**Overhead (c vs b):** tracing I/O and callback cost

## Hardware

(fill in after running)

- CPU:
- RAM:
- Disk:
- OS:
