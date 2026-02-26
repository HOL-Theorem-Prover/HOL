# Proof Trace TODO

### [regression] Regression testing

Figure out how to add automated regression tests for the
proof trace pipeline. Needs to cover: recording produces
valid traces, merge resolves all references, replay produces
oracle-free theorems.

### [richer-exports] Richer export selection for merge

Currently merge only targets explicitly named theorems
(THY.THM pairs). Extend the selection interface:

- **Pull by constant**: include all theorems that mention a
  given constant
- **Pull by type**: include all theorems that mention a given
  type operator
- **Pull by theory**: include all exported theorems from a
  given theory

### [replay-display] Replay display options

- **`--include-defs`**: also print definitional theorems
  (DEF_SPEC/DEF_TYOP) that were replayed as dependencies of
  the target exports. These are already in the merged trace
  and replayed; this flag controls whether they appear in the
  output.

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
