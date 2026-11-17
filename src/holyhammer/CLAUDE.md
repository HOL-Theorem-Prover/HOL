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
called at the bottom of `selftest.sml`, using `testutils`).  There is
no per-test flag; comment out the top-level call to isolate a section.
Sections needing a real prover self-skip when `hhProver.probe` finds
none (they print `OK`), so a green run without provers installed does
**not** exercise proof search.  Some sections gate on env vars
(e.g. `HHEVAL_INTEGRATION_TEST`).  Under the whole-tree build the full
selftest runs only when `HOLSELFTESTLEVEL` is set (see `Holmakefile`).

Prover-parsing tests are hermetic: they replay recorded prover stdout
from `test-data/` rather than invoking a binary.  When you change output
parsing, add/refresh a recording there instead of depending on a live
prover.

`eval/` is scratch output for evaluation runs and is gitignored — never
rely on its contents being present or committed.

## Module map (pipeline order)

- **`hhConfig`** — the `prover` datatype (`Eprover | Vampire |
  Zipperposition | Z3`) and its name codec, the option system
  (`hh_set`/`hh_get`/`snapshot` → `hh_options`), config-file + env
  discovery, executable discovery, and the state dir.  Central; nearly
  everything depends on it, so it must not depend back on later modules.
  Provers are identified by constructor throughout; `prover_name`
  strings appear only at text boundaries (option values, config keys,
  install dirs, journals).
- **`hhTranslate`, `hhTptpProblem`, `hhExportLib`, and the `hhExport*`
  dialect writers** (Fof, Tf0/Tf1, Th0/Th1, Sexpr) — HOL term/goal →
  TPTP dialects (FOF / TFF / THF, mono & poly).
  `hhExportLib` also drives the bushy/chainy dependency-export machinery
  shared with dataset generation.
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
  reconstruction, and returns verified `suggestion`s; stops on first
  success / `max_proofs` / timeout.
- **`hhReconstruct`** — replays the ATP's used axioms as a HOL4 tactic
  (Metis today) and minimizes.  *This layer is under active rework
  toward a preplay ladder — check current code before assuming its
  shape.*
- **`holyHammer`** — user-facing API: `holyhammer : term -> thm`, the
  `hh` tactic, `hh_pb`, and `main_hh` / `main_hh_lemmas` (premise
  selection).  This is the TacticToe integration surface and must keep
  working; consume `main_hh_lemmas` for lemma lists.
- **`hhEval`** — headless, resumable evaluation harness (Bushy/Chainy
  regimes, Deps/kNN selectors, Prover/Sched engines) writing a JSONL
  journal; `run_smoke` backs `smoke.exe`.

## Reused infrastructure (do not rebuild here)

- Premise selection: `src/AI/machine_learning/` — `mlThmData`,
  `mlFeature`, `mlNearestNeighbor` (features, kNN, TF-IDF).
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
