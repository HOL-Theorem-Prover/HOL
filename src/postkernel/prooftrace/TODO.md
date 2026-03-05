# Proof Trace TODO

### [replay-stack] Update replayer for stack encoding

ReplayTrace needs to handle the new format elements:
- Parse `~k` / `^k` references (term and theorem stack refs)
- Maintain term and theorem stacks (circular buffers, depth 16)
- Handle anonymous T entries (no leading ID — push to stack only)
- Handle `Td` lines (define-without-push for late materialisation)
- Implement SPECL / SPECIALIZEL replay (iterated SPEC/Specialize)
- Resolve `~k` / `^k` to actual values via stack lookup

### [merge-stack] Update merge tool for stack encoding

MergeTrace needs to handle the new format in both passes:
- Parse `~k` / `^k` references and SPECL/SPECIALIZEL in dep scan
- For `^k`-only theorems (never referenced by explicit ID), skip
  global ID allocation — they are purely local
- Preserve stack encoding in merged output (use `~k`/`^k` and
  compound rules, don't expand to explicit IDs)
- Handle anonymous T entries and Td lines in Pass 2 remapping

### [metadata-stack] Update TraceMetadata for stack encoding

TraceMetadata.extract needs to handle:
- `~k` / `^k` tokens (skip or resolve during metadata scan)
- SPECL / SPECIALIZEL rule names
- Anonymous T entries (no leading ID)
- Td lines

### [measure-lazy-t] Measure lazy T output impact

Run a tracing build with the lazy T implementation and count:
- Anonymous vs ID'd T entries
- Td materialisations (late fallbacks)
- Total trace size reduction vs previous stack-encoding-only traces

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

### [deletion] Trace recording and constant/type deletion

Trace recording does not handle `delete_const` / `delete_type`
correctly. Several issues:

1. **No delete entries in the trace format**: The trace records
   DEF_SPEC, C, O for constant/type creation but has no entry
   for deletion. If a theory script deletes a constant and
   redefines it, the replay would see two creations with no
   intervening deletion, and the second would fail.

2. **Stale `defined_consts`/`defined_types` sets**: These sets
   track which constants/types were introduced by DEF_SPEC /
   DEF_TYOP, so that the `NewConstant`/`NewTypeOp` TheoryDelta
   hook can suppress redundant C/O lines. However, the sets are
   never pruned on `DelConstant`/`DelTypeOp` deltas. If a
   constant is defined (added to `defined_consts`), deleted,
   then re-introduced via `new_constant` (not `new_definition`),
   the hook suppresses the C line because the name is still in
   `defined_consts`. The replay would then have no introduction
   for the re-created constant.

3. **Interned terms with mutated names**: `retire_id` mutates
   the `kernelid` ref in place, changing the Name to a mangled
   form (e.g., `old0->foo<-old`). Any term interned before
   deletion has a trace entry with the original name, but the
   ML value now carries the mangled name. If the same ML value
   is re-encountered after deletion, it would be re-interned
   with the mangled name (since `dest_thy_const` reads from
   the mutated ref), producing a second trace entry for the
   "same" constant. This is not incorrect per se (the two are
   genuinely different constants at the kernel level), but the
   original trace entry becomes unreplayable if the constant
   no longer exists.

**Practical impact**: delete operations during `--trace` builds
are rare — they are primarily an interactive convenience. If
this becomes an issue, the fix would be:
- Handle `DelConstant`/`DelTypeOp` in the TheoryDelta hook to
  clean up the `defined_consts`/`defined_types` sets
- Add a trace format entry for deletions so replay can mirror
  the delete-and-recreate sequence

Note: the proposed intern caching change (descriptor maps +
hash-indexed pointer-eq cache) is *not* affected by deletion.
The kernelid ref mutation naturally invalidates all cache
layers: `Term.hash` reads from the ref (hash changes),
pointer-eq cache misses (different hash slot), and the
descriptor map produces a different key (mangled name).

### [set-assoc-cache] Set-associative intern cache

The term intern pointer-eq cache is currently direct-mapped
(1-way): each hash slot holds one entry. If two frequently-used
terms hash to the same slot, they evict each other on every
access, falling through to the descriptor path. A 2-way or
4-way set-associative cache (checking 2–4 entries per slot via
pointer_eq) would improve hit rates for such collisions at
negligible extra cost per lookup. Worth benchmarking on large
theories to see if collision-induced misses are significant.

### [replay-fail-fast] Replay should fail fast on errors

`process_line`'s `handle e` catches all exceptions, prints
`REPLAY_FAIL`, and continues. A corrupted or missing entry
silently poisons all downstream thm lookups. Better: fail
fast, or insert a sentinel in `thm_map` that raises a clear
error on lookup.

### [pftm-at-record] Write .pftm at recording time

TraceRecord should write a `.pftm` metadata file alongside
the `.pft` at theory export time (`export_hook`). This requires
accumulating metadata during recording (p_min_id, p_max_id,
name_refs, load_refs, const_defs, type_defs, const_decls,
type_decls, t_const_refs, y_tyop_refs, compute_ids, c_deps,
n_terms, n_types, exports) and calling `TraceMetadata.write`
after writing N/E lines. This eliminates the need to run
`prooftrace extract-metadata` as a separate step.

### [pftm-on-fallback] Write .pftm after fallback extract in merge

When `read_file_metadata` falls back to `TraceMetadata.extract`
(no `.pftm` file), it should write the extracted metadata to
the `.pftm` path so subsequent merge runs skip the expensive
scan. Currently the extracted metadata is used but not persisted.

### [cache-file-deps] Cache liveness-filtered deps for topo sort

`file_deps` (for topo sort in Pass 2) iterates over
`#name_refs`, `#load_refs`, `#t_const_refs`, `#y_tyop_refs`
re-checking liveness for each entry. These lists can be large.
The liveness-filtered dependency set was already computed
during Pass 1 and could be cached rather than recomputed.
