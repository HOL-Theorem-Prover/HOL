# Proof Trace TODO

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

### [direct-replay] Direct unmerged replay for full verification

The merge→replay→load pipeline has ~2× extra .pft I/O
overhead compared to replaying unmerged traces directly. For
the "verify everything" use case (all theories, all exports),
the merge step's liveness pruning provides no benefit, and
the provenance mapping (F/G lines) is unnecessary because
theory identity is inherent in the unmerged traces.

A direct replay path would process each theory's .pft and
.dat together in dependency order:
1. Replay P entries through the kernel
2. Resolve NAME via already-loaded ancestor exports, LOAD via
   already-loaded ancestor theorem maps
3. Populate the Theory structure directly (link_parents,
   DB.bindl, thydata callbacks) using replayed theorems

This avoids the merge step entirely and produces a fully
loaded interactive session in a single pass over the traces.
The merge→replay path remains for targeted verification
(specific exports) where pruning matters.

Worth exploring after the merge-based theory loading is
working, with benchmarks to quantify the actual overhead.

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
