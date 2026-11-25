This file provides guidance to coding agents when working with HolyHammer code in the HOL4 repository.

HOLyHammer: given a HOL4 goal, select premises, translate goal+premises
to TPTP, schedule external-prover slices, and reconstruct the resulting
proof inside HOL4.

## Cardinal invariant

Every advertised proof is re-checked by the HOL4 kernel through Metis
reconstruction — an ATP's SZS verdict is never trusted on its own.  The
hammer introduces no oracle tags; unverified ATP results must stay
clearly marked as such.  Preserve this across any refactor.

## Build & test

From this directory (`src/holyhammer/`):

    ../../bin/Holmake selftest.exe && ./selftest.exe  # unit + integration
    ../../bin/Holmake smoke.exe    && ./smoke.exe      # e2e, needs provers

`selftest.exe` runs every `test_*` section (each a top-level `fun`
called at the bottom of `selftest.sml`, using `testutils` and the
helpers of `hhTestLib`, which `evaluation/selftest.sml` shares).  There
is no per-test flag; comment out the top-level call to isolate a
section.  The selftest launches no real prover; live proof search is
exercised by `smoke.exe` alone, which runs each tested prover alone, the
schedule (and its cache), the MePo/MaSh/MeSh selectors, every typed
slice, and unprovable goals, printing one line per check.  It fails,
naming them, when E, Vampire or Zipperposition is absent; Z3 is only
run, when present, by the runner check.  Under the whole-tree build the
full selftest runs only when `HOLSELFTESTLEVEL` is set (see
`Holmakefile`).

Prover-parsing tests are hermetic: they replay recorded prover stdout
from `test-data/` rather than invoking a binary.  When you change output
parsing, add/refresh a recording there instead of depending on a live
prover.

`evaluation/` holds the evaluation harness `hhEval` with its own
`Holmakefile`, selftest and `README`; it is not in the build sequence,
and nothing in the library may depend on it.  `eval/` is its default
scratch output directory and is gitignored — never rely on its contents
being present or committed.

## Module map (pipeline order)

- **`hhConfig`** — the `prover` datatype (`Eprover | Vampire |
  Zipperposition | Z3`) and its name codec, the option system
  (`hh_set`/`hh_get`/`snapshot` → `hh_options`), config-file + env
  discovery, executable discovery, and the state dir.  Central; nearly
  everything depends on it, so it must not depend back on later modules.
  Provers are identified by constructor throughout; `prover_name`
  strings appear only at text boundaries (option values, config keys,
  install dirs, journals).
- **Premise selection: `hhLearn`, `hhMePo`, `hhFactIndex`,
  `hhStature`** — kNN, MaSh, and MeSh rankings (`hhLearn.rank_filters`),
  MePo relevance filtering, fact lookup by name, and fact statures.
- **Problem generation: `hhProblemGen`, `hhTypeEnc`, `hhLamTrans`,
  `hhMonomorph`, `hhTptpProblem`** — goal + premises → typed TPTP
  (`tf0`/`tf1`/`tx0`/`tx0-`/`th0`/`th1`): type encodings, lambda
  translations, monomorphisation, and the TPTP AST/printer.
- **`hhTranslate`, `hhExportLib`, and the `hhExport*` writers** (Fof,
  Tf0/Tf1, Th0/Th1, Sexpr) — the legacy FOF exporter the schedule still
  uses (`hhExportFof`), and the bushy/chainy dataset exporters
  (`README_EXPORT`).
- **`hhProver`** — declarative prover table: `config_of` maps each
  `prover` constructor to its `prover_config`, which bundles executable
  discovery, version probing, per-slice command construction,
  output/SZS parsing, and slice definitions; `run` / `run_async` execute
  one problem.  Add a prover by adding a constructor and its config, not
  by scripting a binary.  Tests substitute fixture configs with
  `with_override`.
- **`hhSlice`** — turns `hh_options` into the concrete
  `(prover, slice)` schedule and each slice's time budget.
- **`hhCache`** — memoizes prover runs keyed by prover+version+argv+
  problem.
- **`hhSchedule`** — runs slices across cores, emits `event`s, drives
  reconstruction, and returns verified `suggestion`s; stops the search at
  the timeout, and reconstructs the lists found until the run's
  `max_proofs` verify, or, past the timeout, one has (an earlier one
  included).  `max_proofs` is a parameter of the run, not an option.
- **`hhPool`** — bounded pool of worker threads (export workers).
- **`hhReconstruct`** — replays the ATP's used axioms with Metis
  (preplay, drop-one retries), minimizes, and names the lemmas for the
  printed call.
- **`holyHammer`** — user-facing API: `holyhammer : term -> thm`, the
  `hh` tactic, `hh_pb`, and `main_hh` / `main_hh_lemmas` (premise
  selection).  This is the TacticToe integration surface and must keep
  working; consume `main_hh_lemmas` for lemma lists.
- **`evaluation/hhEval`** (outside the library) — headless, resumable
  evaluation harness (Bushy/Chainy regimes, Deps/kNN/MePo/MaSh/MeSh
  selectors, Prover/Sched engines) writing a JSONL journal.

## Reused infrastructure (do not rebuild here)

- Features, kNN, TF-IDF, and theorem data: `src/AI/machine_learning/` —
  `mlThmData`, `mlFeature`, `mlNearestNeighbor`.
- Training/dependency data: kernel `Dep` (`src/prekernel/Dep.sml`).
- `psMinimize`, `smlTimeout` from the ML/proof-search libraries.

## Boundaries & conventions

- Modules use the `hh` prefix; keep the `holyhammer`/`hh` entry-point
  names stable — integrations depend on them.
- Fact identity for learning follows `nickname_of_thm`: qualified
  theorem name, else name + hash of the printed term.  Correctness must
  never depend on freshness of learning/cache data — staleness may only
  degrade ranking, never soundness.
- Avoid hardcoding tuning values (slice counts, premise counts, prover
  timeouts) as invariants; they are options/registry data and change.
