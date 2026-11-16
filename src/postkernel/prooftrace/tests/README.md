# Prooftrace regressions

Run the encountered-bug fixtures with an exporter-capable tracing HOL:

```sh
/path/to/HOL/src/postkernel/prooftrace/tests/run.sh all \
  /path/to/tracing/bin/hol /scratch/prooftrace
```

The suites are `identity`, `oracle`, `export`, `compute-binder`, `term-kind`,
`mk-abs`, and `closedness`. Each also runs separately in place of `all`.
Sources load from this checkout; fresh processes check HOL replay. Logs and
outputs stay in the scratch dir. `compute-binder` needs `cv_computeLib`.
Identity fixtures need a producer rebuilt with export/import hooks.

Use a Candle checkout containing [Candle PR #25] for the PFT 0.1.0
reader and check script.

[Candle PR #25]: https://github.com/CakeML/candle/pull/25

Candle checks the exact sequents of the `candle` ruleset outputs, including
`compute-binder`'s, by replaying them. Its `candle/pft/check.sh` converts
their prerequisites with this checkout and the tracing HOL, then replays:

```sh
/path/to/Candle/candle/pft/check.sh /path/to/HOL /path/to/tracing \
  /scratch/prooftrace
```
