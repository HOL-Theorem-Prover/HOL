# Proof Trace Implementation Status

## Recently completed

- TraceRecord.sml rewritten (#1-8): H line, no debug prints,
  no dead code, cleaner naming, cached compression detection
- ReplayTrace.sml lazy construction in place, prim_new fallbacks
  removed (#12, #9-11)
- MergeTrace.sml rewritten (#13): sparse P entry IDs via
  Redblackmap, H line parsing for heap ancestry, automatic heap
  trace file discovery, proper topological sort of output files,
  per-file liveness with iterative ancestor processing
- Stale temp file cleanup: stale stream handler removes leftover
  temp files before opening a new output
- Unresolved parent trace_ids are now hard errors in merge
- H lines documented as absolute paths in DESIGN.md
- Compression removed from recording/merging/replay: all files
  written as plain .pft; external tools can compress if desired
- prooftrace binary moved from src/boss to
  src/postkernel/prooftrace (#14 partial): built on hol.state.min
  with kernel-only deps, no longer depends on hol.state or
  bossLib. Removed --load, --load-hol, --verbose options.
  Default mode loads Parse in subprocess for term printing.
  --concise for names only. --interactive for bare REPL.

## Remaining implementation

### Anonymous thydata theorem references (#18)

When theories are loaded from disk, anonymous theorems embedded
in thydata (TypeBase entries, simpset theorems, etc.) are loaded
via `Thm.disk_thm`. These theorems have depids beyond the range
of named exports (e.g., prim_rec has 47 named exports with
depids 0–46, but thydata theorems get depids 47+). The old code
generated `_unknown_thy_N` names which couldn't be resolved
during merge.

**Design (agreed):** Introduce `DISK_DEP` rule and `D` export
lines. See DESIGN.md for full details. Summary:
- `Thm.save_dep` accumulates `(depid_number, thm)` into a ref
  when tracing is active (populated during .dat file write)
- `trace_export` passes this list to the export hook
- TraceRecord emits `D <depid> <trace_id>` lines for anonymous
  theorems (depids not covered by named exports)
- `ThyDataSexp.thmreader` signals anonymous theorems via
  `TR_DISK_DEP` instead of `TR_DISK_THM`
- TraceRecord emits `DISK_DEP <thy> <depid>` in consuming traces
- MergeTrace resolves `DISK_DEP` via `D` lines in ancestor traces

**Implementation changes needed:**
1. `Thm.sml`: add `save_dep_log` ref, accumulate when
   `trace_hook` is active, expand `trace_export` signature
   to pass the log
2. `Thm.sml`: add `TR_DISK_DEP` variant to `trace_record`
3. `ThyDataSexp.sml`: `thmreader` fallback uses `TR_DISK_DEP`
   with depid number instead of `_unknown` name
4. `TraceRecord.sml`: handle `TR_DISK_DEP`, emit `D` lines in
   export hook
5. `MergeTrace.sml`: parse `D` lines, build depid resolution
   map, handle `DISK_DEP` rule
6. `ReplayTrace.sml`: parse `DISK_DEP` (same semantics as
   `DISK_THM` — just a reference to an already-replayed theorem)

### Replay-aware theory loading (#14 remaining)

After replay, loading HOL libraries (for pretty-printing and
interactive use) must not conflict with what replay has already
established in the kernel. Normally, `TheoryReader.load_thydata`
calls `incorporate_types` / `incorporate_consts` (which register
types/constants in the kernel) and reconstructs theorems from
`.dat` files as DISK_THMs. But replay has already defined the
same types, constants, and theorems via kernel inference rules.

We need a replay-aware theory loading mode where:
- `incorporate_types` / `incorporate_consts` reuse the types
  and constants already present in the kernel (from replay's
  DEF_TYOP / DEF_SPEC steps) rather than creating new ones
- Theorems are populated from the replayed theorem values
  rather than reconstructed from `.dat` files as DISK_THMs
- `DB.bindl`, `Theory.link_parents`, `load_complete` etc.
  still fire normally so that Parse grammars, TypeBase,
  simpsets, and other hooks are set up correctly

This requires:
1. A mapping from (theory, name) to replayed thm values,
   built from the E lines during replay
2. A way for TheoryReader (or a wrapper) to use this mapping
   instead of `.dat` file reconstruction
3. Ensuring kernel type/const registration is idempotent or
   skipped when the type/const already exists from replay

Once this is in place, the prooftrace replay command can:
- Load full HOL libraries after replay for pretty-printing
  (default verbose mode with proper term printing)
- Provide `--interactive` with Theory structures populated
  by replayed theorems

### Temp file cleanup on failed/killed builds (#20)

Temp files (`.hol/objs/.trace_*.tmp`) are not cleaned up when
a build process is killed (SIGKILL) since `atExit` handlers
don't run. Being under `.hol/` they are hidden from git and
swept by `Holmake cleanAll`. Could also have Holmake clean
them before each theory build.

Note: `.hol/objs` path is hardcoded in TraceRecord, matching
`HFS_NameMunge.HOLOBJDIR`. If the Holmake directory layout
changes, TraceRecord needs updating. Ideally TraceRecord would
use `HOLFileSys` but it's not available at kernel level.

### End-to-end testing

The MergeTrace rewrite needs testing with actual trace files
from a `--trace` build. Key scenarios:

1. Single theory with no heap deps (simplest case)
2. Theory referencing ancestor theories via DISK_THM
3. Theory referencing parent heap via unresolved trace_ids
4. Multiple theories sharing a heap ancestry chain
5. COMPUTE entries with C init line remapping
