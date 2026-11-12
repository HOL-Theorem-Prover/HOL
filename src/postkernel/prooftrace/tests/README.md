# Prooftrace export regressions

Run a fixture with a tracing HOL built using exporter-capable Poly/ML:

```sh
/path/to/HOL/src/postkernel/prooftrace/tests/run.sh oracle \
  /path/to/tracing/bin/hol /scratch/prooftrace
```

The suites are `identity`, `oracle`, `export`, `compute-binder`,
`term-kind`, `mk-abs`, and `closedness`; `all` runs them together. Sources
load from this checkout, with separate processes for fresh kernel state and
logs in the scratch dir.
`compute-binder` also needs `cv_computeLib`.

`run.sh` performs native export, converts both rulesets and runs the HOL
checks. It does not run Candle. Actual Candle validation requires replaying
the Candle outputs with their prerequisites and running the `.ml` checkers
listed below in Candle.

For example, after running the `oracle` suite, convert its public prerequisite
with the same checkout. Replace the absolute paths below for your builds:

```sh
/path/to/HOL/src/postkernel/prooftrace/pft preamble \
  --output /scratch/prooftrace/preamble.pft
/path/to/HOL/src/postkernel/prooftrace/pft emit --ruleset candle \
  --trace /path/to/tracing/src/bool/.hol/objs/boolTheory.tr.gz \
  --output /scratch/prooftrace/bool.candle.pft
```

Candle's `replay.ml` ends with an example replay. Make a scratch driver that
replaces that example and uses absolute input paths:

```sh
sed -e 's|let here = "candle/pft/";;|let here = "";;|' \
  -e 's|let extract_footer_path = here \^ "extract_footer";;|let extract_footer_path = "/path/to/Candle/candle/pft/extract_footer";;|' \
  -e '/^let _ = replay_all \[/d' \
  /path/to/Candle/candle/pft/replay.ml > /scratch/prooftrace/check.ml
cat >> /scratch/prooftrace/check.ml <<'EOF'
replay_all ["/scratch/prooftrace/preamble.pft";
            "/scratch/prooftrace/bool.candle.pft";
            "/scratch/prooftrace/oracle/oracle_hyps.candle.pft.bin";
            "/scratch/prooftrace/oracle/oracle_retired_instance.candle.pft"];;
#use "/path/to/HOL/src/postkernel/prooftrace/tests/oracle-check-results.ml";;
check_oracle_results ();;
EOF
cd /path/to/Candle/candle/build
./cake --candle < /scratch/prooftrace/check.ml \
  > /scratch/prooftrace/candle.log 2>&1
```

Use the Candle build's `extract_footer` executable. Check that the log contains
`PFT_ORACLE_ALL_CHECKS_PASSED` and no `EXCEPTION`; the runtime can exit zero
after an exception. The other suites use this same preamble→prerequisites→
fixture→checker sequence with the files and extra prerequisites listed below.

* `closedness` reproduces the closedness sentinel collision for a closed
  abstraction containing another closed abstraction. It also checks that an
  unvisited term retains its sentinel.
* `oracle` reproduces lost hypotheses, synthetic binder capture in an
  oracle-only sequent and a local polymorphic constant first used at a
  monomorphic type. A fresh minimal HOL checker compares the complete
  oracle sequent and retains both `oracle_hyps.pft.bin` and
  `oracle_hyps.candle.pft.bin`. It also rejects incompatible types of a retired
  undefined constant while accepting instances of a generic first occurrence.
  Replay the accepted `oracle_retired_instance.candle.pft` too, as above;
  `oracle-check-results.ml` checks both fixtures.
* `export` checks specification binders: an unused existential, shadowing,
  and an inner binder named like the introduced constant. It also reproduces
  hypothesis collisions in CONJ, MP, DISJ_CASES and CHOOSE, and GEN_ABS with a
  polymorphic LET result. A fresh minimal HOL phase replays `bool` and all
  five fixtures and compares their exact sequents. Replay their Candle
  outputs after `bool`, then run `export-check-candle.ml` for the same checks.
* `compute-binder` checks coincident binder names, delayed substitution,
  a numeral beyond machine integer range, and COMB/ABS capture confusion.
  Replay the traced ancestors through `cv` with the logical and compute
  preambles, then run `compute-binder-check.ml` for the four exact sequents.
* `term-kind` checks distinct COMB/ABS nodes with identical children during
  substitution and specification, and empty-named binder capture. After replay
  of `bool` and the fixture, run `term-kind-check.ml` in Candle. The suite
  runs `term-kind-check.sml` itself in a fresh minimal HOL replay phase.
* `mk-abs` reproduces a clashing cosmetic abstraction binder whose converted
  name differs from the raw proof's opened binder. It checks the exact sequent
  in a fresh minimal heap. The converter emits `ABS` and `TRANS` for the
  mismatch; matching binders still use `Mk_abs`. The test also checks those
  instructions at each theorem's `SAVE`, so the replayer's compatibility
  repair cannot hide an inverted instruction choice.

The `.ml` checkers run in Candle; their producer programs run in HOL.

## Exported identities

`identity` needs a producer genuinely rebuilt with the export/import hooks;
loading a new `Tracing` structure does not change the instance already used
by `Theory.export_theory`.

The identity suite retains the raw producer/loader regressions and also
converts their outputs. It compares all seven exact exported sequents and
required public/private names through raw HOL and separate HOL PFT replay.
It also converts an already-negated `NOT_INTRO` premise to Candle. Replay
`bool` and `identity_negation.candle.pft` after the logical preamble, then
run `identity-check-candle.ml` to check that theorem's exact sequent.
