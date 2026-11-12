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

Candle replay is separate. First convert its public prerequisites with this
checkout's [driver](../pft-cli.md):

```sh
/path/to/HOL/src/postkernel/prooftrace/pft.sh preamble \
  --output /scratch/prooftrace/preamble.pft
/path/to/HOL/src/postkernel/prooftrace/pft.sh emit --ruleset candle \
  --trace /path/to/tracing/src/bool/.hol/objs/boolTheory.tr.gz \
  --output /scratch/prooftrace/bool.candle.pft
```

Computation additionally needs the traced ancestors through `cv`. Convert
these traces to `/scratch/prooftrace/<theory>.candle.pft` in this order:

```sh
pft_driver=/path/to/HOL/src/postkernel/prooftrace/pft.sh
pft_tracing=/path/to/tracing
for pft_input in \
  marker/marker num/theories/num metis/normalForms combin/combin \
  simp/src/boolSimpsContext HolSat/sat refute/canonContext \
  metis/normalFormsContext metis/folToolsContext metis/folMappingContext \
  meson/src/mesonLibContext meson/src/Canon_Port_Context \
  IndDef/InductiveDefinitionContext relation/relation \
  num/theories/prim_rec quotient/src/quotient coretypes/pair \
  num/theories/arithmetic coretypes/sum coretypes/one coretypes/option \
  num/theories/While num/theories/numeral num/theories/cv
do
  "$pft_driver" emit --ruleset candle \
    --trace "$pft_tracing/src/${pft_input%/*}/.hol/objs/${pft_input##*/}Theory.tr.gz" \
    --output "/scratch/prooftrace/${pft_input##*/}.candle.pft"
done
"$pft_driver" compute-preamble --output /scratch/prooftrace/compute-preamble.pft
```

The following runs every supported Candle checker. Keep the input order:
the logical prerequisites precede the fixtures; computation ancestors precede
the compute preamble and computation fixture.

```sh
sed -e 's|let here = "candle/pft/";;|let here = "";;|' \
  -e 's|let extract_footer_path = here \^ "extract_footer";;|let extract_footer_path = "/path/to/Candle/candle/pft/extract_footer";;|' \
  -e '/^let _ = replay_all \[/d' \
  /path/to/Candle/candle/pft/replay.ml > /scratch/prooftrace/check.ml
cat >> /scratch/prooftrace/check.ml <<'END'
#use "/path/to/HOL/src/postkernel/prooftrace/tests/check-candle.ml";;
let inputs names = replay_all (List.map
  (fun name -> "/scratch/prooftrace/" ^ name) names);;
inputs ["preamble.pft"; "bool.candle.pft"];;
inputs ["oracle/oracle_hyps.candle.pft";
        "oracle/oracle_retired_instance.candle.pft"];;
check_oracle_results ();;
inputs ["export/vacuous.candle.pft"; "export/shadow.candle.pft";
        "export/overlap.candle.pft"; "export/hypotheses.candle.pft";
        "export/binder.candle.pft"];;
check_export_results ();;
inputs ["term-kind/term-kinds.candle.pft"];;
term_kind_check ();;
inputs ["identity/identity_negation.candle.pft";
        "identity/identity_type_names.candle.pft"];;
check_identity_results ();;
inputs ["marker.candle.pft"; "num.candle.pft"; "normalForms.candle.pft";
        "combin.candle.pft"; "boolSimpsContext.candle.pft"; "sat.candle.pft";
        "canonContext.candle.pft"; "normalFormsContext.candle.pft";
        "folToolsContext.candle.pft"; "folMappingContext.candle.pft";
        "mesonLibContext.candle.pft"; "Canon_Port_Context.candle.pft";
        "InductiveDefinitionContext.candle.pft"; "relation.candle.pft";
        "prim_rec.candle.pft"; "quotient.candle.pft"; "pair.candle.pft";
        "arithmetic.candle.pft"; "sum.candle.pft"; "one.candle.pft";
        "option.candle.pft"; "While.candle.pft"; "numeral.candle.pft";
        "cv.candle.pft"; "compute-preamble.pft";
        "compute-binder/compute-binders.pft.bin"];;
check_compute_results ();;
print_endline "ALL_CANDLE_PASS";;
END
cd /path/to/Candle/candle/build
./cake --candle < /scratch/prooftrace/check.ml \
  > /scratch/prooftrace/candle.log 2>&1
grep -q 'ALL_CANDLE_PASS$' /scratch/prooftrace/candle.log
! grep -q 'EXCEPTION' /scratch/prooftrace/candle.log
```

Use Candle's built `extract_footer`. The runtime can exit zero after an
exception, so both log checks matter. `mk-abs` and `closedness` run native
checks only. Identity fixtures need a producer rebuilt with export/import
hooks.
