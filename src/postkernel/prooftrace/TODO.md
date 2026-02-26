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

### [eager-iline] Over-eager I-line marking in merge

`mark_live` marks the I (compute init) line's term/type deps
whenever the file is processed for any reason, not only when
a COMPUTE entry is live. The comment claims "The C file is
only ever processed when a COMPUTE entry is live" but a heap
file containing the I line can be processed for unrelated
reasons (e.g., heap parent resolution for non-COMPUTE thms).
This causes unnecessary entries in the merged output. Fix:
guard the I-line term/type marking on `!found_compute` or
track separately whether the file's COMPUTE entries are live.

### [rule-table] Table-driven rule argument dispatch in merge

`extract_parent_ids`, `extract_term_ids`, `extract_type_ids`,
and `remap_args` each independently switch on the rule name
string (~400 lines of repetitive code). A single table mapping
rule name to argument schema (which positions are P, T, Y, or
string) would replace all four functions and make it impossible
to have inconsistencies between them (e.g., adding a rule to
one but forgetting another).

### [p-liveness-array] Dense array for P liveness in merge

`mark_live` uses `PIntMap` (Patricia trees) for P liveness
and `p_remap`. Since `p_base_id` and `p_max_id` are known,
a bool array of size `(max - base + 1)` would give O(1)
operations and better cache behavior. The `p_offsets` array
already uses this scheme.

### [trace-parse] Factor out shared parsing utilities

`tokenize` and `unescape` are shared between `ReplayTrace`
and `MergeTrace` via `val tokenize = ReplayTrace.tokenize`.
A dedicated `TraceParse` module would be cleaner.

### [dup-cmp] Deduplicate comparison functions

`thyname_cmp` is defined identically in `MergeTrace`,
`ReplayTrace`, and in `TraceRecord`'s `reset_for_new_session`.
The `Redblackset.empty` with inline comparison functions is
copy-pasted 3 times in `TraceRecord`. Extract once.

### [stale-check] Avoid per-step stale stream check

Every `record_hook` call starts with `check_stale()`, which
attempts a zero-byte `TextIO.output` to probe the stream.
After the first successful write in a session, this always
succeeds. A boolean flag set after the first successful check
would eliminate this per-step overhead.

### [replay-fail-fast] Replay should fail fast on errors

`process_line`'s `handle e` catches all exceptions, prints
`REPLAY_FAIL`, and continues. A corrupted or missing entry
silently poisons all downstream thm lookups. Better: fail
fast, or insert a sentinel in `thm_map` that raises a clear
error on lookup.

### [cache-file-deps] Cache liveness-filtered deps for topo sort

`file_deps` (for topo sort in Pass 2) iterates over
`#name_refs`, `#load_refs`, `#t_const_refs`, `#y_tyop_refs`
re-checking liveness for each entry. These lists can be large.
The liveness-filtered dependency set was already computed
during Pass 1 and could be cached rather than recomputed.
