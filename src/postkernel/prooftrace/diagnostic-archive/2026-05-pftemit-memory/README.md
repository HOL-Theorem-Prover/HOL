# PFTEmit memory diagnostic archive (May 2026)

This directory preserves the temporary instrumentation used for the 60-theory
CakeML/Candle memory investigation. It is intentionally not part of the normal
`PFTEmit` implementation.

## Contents

- `PFTEmit-diagnostics.patch`: instrumentation layered on top of HOL commit
  `f859c3ec0` (`Add more to emit-candle-merged`).
- `diagnose-candle-emit.sh`: stratified sampling, execution, and CSV-summary
  helper for an emitter built with that instrumentation.

The patch adds only diagnostic behavior: phase RSS/HWM readings, per-export
statistics, primitive-command counts, and memo/free-information counters. The
active `PFTEmit.sml` was restored to the committed production version after
this patch was captured.

## Applying it

From the HOL repository root at the recorded base commit:

```sh
git apply src/postkernel/prooftrace/diagnostic-archive/2026-05-pftemit-memory/PFTEmit-diagnostics.patch
```

The patch was generated with:

```sh
git diff --binary -- src/postkernel/prooftrace/PFTEmit.sml
```

If the production source has changed, apply it on a temporary worktree at
`f859c3ec0`, or inspect/rebase the patch manually rather than assuming it still
applies cleanly.

## Running it

After the user has built the instrumented emitter:

```sh
cd src/postkernel/prooftrace
TIMEOUT=300 diagnostic-archive/2026-05-pftemit-memory/diagnose-candle-emit.sh \
  run ./emit-candle-merged 60 diaglogs

diagnostic-archive/2026-05-pftemit-memory/diagnose-candle-emit.sh \
  summarize diaglogs > diaglogs-summary.csv
```

The script removes each sampled theory's existing `.candle.pft.bin` before
emission. Runs are serial, although `emit-candle-merged` itself supports
parallel full-pipeline operation.

## Results and conclusions

The raw `diaglogs3` directory was a generated local artifact and is not included
here. The durable measurements, interpretation, and proposed follow-up
experiments are documented in:

- `../../PFTEmit-memory-diagnostics-plan.md`
- `../../PFTEmit-optimisation-notes.md`
- `../../PFTEmit-PFTMerge-review.md`

The principal next experiment identified by the sample was testing a flat array
for the very large source-theorem memo (`th_memo`) while retaining a mixed
CakeML/Vyper benchmark suite. That experiment has not been implemented here.
