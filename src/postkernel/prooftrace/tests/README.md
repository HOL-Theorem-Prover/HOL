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

Candle replay is separate. For the `oracle` suite, first convert its public
prerequisites with this checkout's [driver](../pft-cli.md):

```sh
/path/to/HOL/src/postkernel/prooftrace/pft.sh preamble \
  --output /scratch/prooftrace/preamble.pft
/path/to/HOL/src/postkernel/prooftrace/pft.sh emit --ruleset candle \
  --trace /path/to/tracing/src/bool/.hol/objs/boolTheory.tr.gz \
  --output /scratch/prooftrace/bool.candle.pft
sed -e 's|let here = "candle/pft/";;|let here = "";;|' \
  -e 's|let extract_footer_path = here \^ "extract_footer";;|let extract_footer_path = "/path/to/Candle/candle/pft/extract_footer";;|' \
  -e '/^let _ = replay_all \[/d' \
  /path/to/Candle/candle/pft/replay.ml > /scratch/prooftrace/check.ml
cat >> /scratch/prooftrace/check.ml <<'END'
replay_all ["/scratch/prooftrace/preamble.pft";
            "/scratch/prooftrace/bool.candle.pft";
            "/scratch/prooftrace/oracle/oracle_hyps.candle.pft";
            "/scratch/prooftrace/oracle/oracle_retired_instance.candle.pft"];;
#use "/path/to/HOL/src/postkernel/prooftrace/tests/check-candle.ml";;
check_oracle_results ();;
print_endline "ORACLE_CANDLE_PASS";;
END
cd /path/to/Candle/candle/build
./cake --candle < /scratch/prooftrace/check.ml \
  > /scratch/prooftrace/candle.log 2>&1
grep -q 'ORACLE_CANDLE_PASS$' /scratch/prooftrace/candle.log
! grep -q 'EXCEPTION' /scratch/prooftrace/candle.log
```

Use Candle's built `extract_footer`. The runtime can exit zero after an
exception, so both log checks matter. The other `check-candle.ml` functions
check their named fixtures after replay with the same prerequisites;
computation also needs the traced ancestors through `cv` and the compute
preamble. Identity fixtures need a producer rebuilt with export/import hooks.
