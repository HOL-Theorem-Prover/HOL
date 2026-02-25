# Proof Trace TODO

## Remaining

### [cross-repo] Cross-repo end-to-end test

Test the full pipeline on a large cross-repository theorem,
e.g. something from CakeML. Should include multiple target
theorems to verify the merge handles multi-export traces and
cross-repo theory dependencies correctly.

### [benchmarks] Performance benchmarks

Measure overhead and performance on large developments:
- **Build overhead**: `develop` vs tracing off; tracing on vs
  tracing off (wall time and trace file sizes)
- **Merge performance**: wall time and memory for merging
  traces across many theories
- **Replay performance**: wall time and memory for replaying
  large merged traces

### [regression] Regression testing

Figure out how to add automated regression tests for the
proof trace pipeline. Needs to cover: recording produces
valid traces, merge resolves all references, replay produces
oracle-free theorems.

### [richer-exports] Richer export selection and display

Currently merge/replay only targets explicitly named theorems.
Extend the interface:

- **Auto-include definitional theorems**: automatically include
  all definitional theorems (DEF_SPEC) for the constants used
  in the target theorem, transitively. These are included as
  named exports so they appear in the replay output.
- **`--verbose` mode**: print the auto-included definitions in
  the replay output (not just the requested target theorems)
- **Pull by constant**: option to include all theorems that
  mention a given constant
- **Pull by type**: option to include all theorems that
  mention a given type operator
- **Pull by theory**: option to include all exported theorems
  from a given theory
- **Multiple targets**: already supported via merge; ensure
  the interface exposes all of them cleanly
- In `--interactive` mode, bind all the above as named values

### [search-dirs] Fix -d flag and help text

- `-d .` (current directory) should always be included in the
  search path even when other `-d` flags are specified
- Help text should clarify that `-d` recursively searches
  subdirectories for trace files

### [theory-loading] Replay-aware theory loading

After replay, loading HOL libraries (for pretty-printing and
interactive use) must not conflict with what replay has already
established in the kernel. Normally, `TheoryReader.load_thydata`
calls `incorporate_types` / `incorporate_consts` and
reconstructs theorems from `.dat` files as DISK_THMs. But
replay has already defined the same types, constants, and
theorems via kernel inference rules.

We need a replay-aware theory loading mode where:
- Types/constants already present are reused, not recreated
- Theorems are populated from replayed values, not `.dat` files
- DB.bindl, Theory.link_parents, etc. still fire so grammars,
  TypeBase, simpsets are set up correctly

### [compression] Automatic compression

Trace files compress ~4:1. Add automatic compression via a
`TraceCompress` module that encapsulates tool selection,
compression, decompression, and file discovery. See DESIGN.md
for full details.

Summary:
- `HOL_PFT_COMPRESS` env var: `zstd` (default), `gzip`,
  `zip`, or `none`
- Compress after recording (both theory and heap traces)
- Decompress transparently on read via `open_trace`
- `atExit` handler cleans up decompression temp files
- Gitignore patterns use `*.pft*` to cover all extensions

Implementation:
1. `TraceCompress.sml`: new module with compress/open_trace/
   find_trace/trace_extensions
2. `TraceRecord.sml`: call `TraceCompress.compress` in
   export_hook and heap cleanup
3. `MergeTrace.sml`: use `TraceCompress.open_trace` with
   cached cleanup across two passes
4. `ReplayTrace.sml`: use `TraceCompress.open_trace`
5. Merge tool file discovery: use `TraceCompress.find_trace`
   and `trace_extensions`
6. Gitignore updates for heap traces

### [tmp-cleanup] Temp file cleanup on killed builds

Temp files (`.hol/objs/.trace_*.tmp`) aren't cleaned on
SIGKILL. Low priority — they're hidden under `.hol/` and
swept by `Holmake cleanAll`.

### [thm-dedup] Theorem dedup in merge

Dedup P entries with identical remapped arguments
(derivation-based) or identical statements (statement-based).

### [memory] Memory optimization in replay

Last-reference pass to null out entries after final use, or
merge-side entry reordering to minimize peak live set.
