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
Identity and oracle also check selected exact sequents after merged HOL
replay; declarations unused by those targets may be pruned.
Identity fixtures need a producer rebuilt with export/import hooks.

Candle replays the `candle` ruleset outputs, including `compute-binder`'s,
and checks their exact sequents with the [Candle recipe].

[Candle recipe]: https://github.com/dnezam/candle-self-verification/blob/0ef20dad16efd20f999c8840ba225636cad2154b/hol-regressions/README.md
