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
- Heap trace compression: atExit handler now compresses heap
  .pft files (zstd > gzip > uncompressed), matching theory traces
- Stale temp file cleanup: stale stream handler removes leftover
  temp files before opening a new output
- Unresolved parent trace_ids are now hard errors in merge
- H lines documented as absolute paths in DESIGN.md

## Remaining implementation

### ThyDataSexp name lookup (#18)

Some DISK_THM entries have `_unknown_thy_N` names because
`ThyDataSexp.thmreader`'s `lookup_name` function fails to find
the theorem in `DB.thms` by depid. Need to diagnose why the
depid doesn't match and fix the lookup.

This is a recording correctness issue — the theorem exists in
the source theory under a valid name, but we can't find which
name at recording time.

### prooftrace binary location and pretty-printing (#14)

**Current situation:**

The `bin/prooftrace` binary is built in `src/boss` with
`-b hol.state`, even though MergeTrace and ReplayTrace only
depend on the kernel. The binary itself just generates a script
and launches `bin/hol --min` as a subprocess — it doesn't need
HOL libraries linked in.

**Plan:**

1. Build `prooftrace` earlier, alongside `hol.state.min` in
   `src/postkernel/prooftrace/`, using only kernel deps.

2. The replay subprocess starts on `hol.state.min` (bare
   kernel, no theories loaded). It replays the trace from
   scratch, independently verifying all theorems.

3. After replay, load full HOL libraries (bossLib etc.)
   normally. This loads theories from `.dat` files (separate
   from the replayed theorems), sets up Parse grammars,
   pretty-printers, TypeBase, etc. The replayed theorems are
   separate ML values but represent the same mathematical
   content — the point of replay is to verify derivability,
   not to replace the theory infrastructure.

4. Default behaviour: verbose output (print each export's
   statement using the loaded pretty-printer). Use `--concise`
   to just list names. Use `--bare` to skip loading HOL
   libraries (raw Term.term_to_string only).

5. For `--interactive` mode: the user gets a full HOL session
   with all normal libraries loaded, plus the replayed
   theorems bound as `prooftrace_exports`.

**Theory loading in replay mode:**

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

This is needed for both `--verbose` (pretty-printing) and
`--interactive` (full HOL session with replayed theorems
populating Theory structures).

### End-to-end testing

The MergeTrace rewrite needs testing with actual trace files
from a `--trace` build. Key scenarios:

1. Single theory with no heap deps (simplest case)
2. Theory referencing ancestor theories via DISK_THM
3. Theory referencing parent heap via unresolved trace_ids
4. Multiple theories sharing a heap ancestry chain
5. COMPUTE entries with C init line remapping
