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
  temp files before opening a new output (only .tmp files deleted;
  completed .pft heap traces preserved)
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
- Anonymous thydata theorem references (#18): DISK_DEP rule and
  D export lines for anonymous thydata-embedded theorems
- Heap trace generation: HOL_TRACE_PROOFS propagated via
  extend_env; stale stream handler no longer deletes completed
  heap traces
- Cross-file DEF_TYOP/DEF_SPEC resolution: merge pulls in
  ancestor theory definitions when types/constants are used in
  a different file from their definition

## Remaining implementation

### Anonymous thydata theorem references (#18) — DONE

Implemented: DISK_DEP rule, D export lines, save_dep_log
accumulation, ThyDataSexp fallback, MergeTrace resolution.
See "Recently completed" above.

### Constant and type declarations in trace (#22)

Replay fails when constructing terms/types whose constants or
type operators were introduced by `new_constant`/`new_type`
(no associated definition theorem). These declarations are not
currently traced. Example: `bool$ARB` is introduced by
`new_constant("ARB", alpha)` with no DEF_SPEC.

**Design (agreed):** Introduce NC/NY line types. See DESIGN.md
for full format and trace-time filtering details. Summary:

- TraceRecord hooks `NewConstant`/`NewTypeOp` TheoryDelta events
- Maintains sets of constants/types already introduced by
  DEF_SPEC/DEF_TYOP (populated when emitting those P lines)
- NC emitted only when constant has no DEF_SPEC; NY only when
  type has no DEF_TYOP (trace-time filtering — no redundancy)
- Ordering is correct: DEF_SPEC/DEF_TYOP fires before
  NewConstant/NewTypeOp for definitions, and NC/NY fires
  before any use for bare declarations

**Merge changes:**
- Parse NC/NY lines during `read_file_data`
- When a live T references a constant: look for DEF_SPEC first
  (local or cross-file); if not found, look for NC (local or
  cross-file). Same for types: DEF_TYOP then NY.
- NC lines also mark their referenced type as live
- Pass 2 emits NC/NY lines for live entries with remapped
  type IDs

**Replay changes:**
- NC: call `Term.prim_new_const {Thy, Name} ty`
- NY: call the appropriate kernel function to declare the type

**Implementation files:**
1. `TraceRecord.sml`: TheoryDelta hook, DEF_SPEC/DEF_TYOP
   tracking sets, NC/NY emission
2. `MergeTrace.sml`: NC/NY parsing, liveness, cross-file
   resolution, Pass 2 output
3. `ReplayTrace.sml`: NC/NY handling

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

### Automatic compression of theory traces (#21)

Theory trace files (`.hol/objs/<thy>Theory.pft`) can be large.
Add optional automatic compression using an external tool
detected at configure time.

**Configure-time detection:**
- Smart configure probes for `zstd`, `gzip`, `lz4` (in
  preference order; zstd recommended for speed/ratio)
- Store the detected tool path and decompression command in
  a config structure (e.g., `Globals.pft_compress` or a
  `SystemConfig` entry) that persists into heaps

**Compression (recording side):**
- Theory traces only (not heap traces, to avoid extension
  proliferation in gitignored heap paths)
- In TraceRecord's export hook, after renaming to the final
  `.pft` path, shell out via `OS.Process.system` to compress
  and remove the original: e.g., `zstd foo.pft && rm foo.pft`
- Final file: `.hol/objs/<thy>Theory.pft.zst` (or `.gz`)
- No-op if no compression tool was detected at configure time

**Decompression (merge/read side):**
- `ReplayTrace.open_trace` (used by both MergeTrace and
  ReplayTrace) probes for compressed variants when the
  uncompressed `.pft` doesn't exist (check `.pft.zst`,
  `.pft.gz` in order)
- Decompress to a temp file via `OS.Process.system`, then
  open the temp file with `TextIO.openIn`. Fully portable
  (no `Posix` or `Unix` structure needed)
- For MergeTrace's two-pass reading, cache the decompressed
  temp path keyed by source path — decompress once, read
  twice, clean up at the end of merge
- Heap trace discovery (`find_heap_trace_file`) does not
  need to handle compression (heap traces are uncompressed)

### End-to-end testing

The MergeTrace rewrite needs testing with actual trace files
from a `--trace` build. Key scenarios:

1. Single theory with no heap deps (simplest case)
2. Theory referencing ancestor theories via DISK_THM
3. Theory referencing parent heap via unresolved trace_ids
4. Multiple theories sharing a heap ancestry chain
5. COMPUTE entries with C init line remapping
