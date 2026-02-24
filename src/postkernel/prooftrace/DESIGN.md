# HOL4 Proof Trace System

## Overview

The proof trace system records kernel inference steps during HOL4
builds and produces self-contained trace files that can be replayed
from scratch for independent verification.

The pipeline has three stages:
1. **Recording**: per-theory `.pft` files produced during
   `HOL_TRACE_PROOFS=1` builds
2. **Merging**: per-theory traces combined into a single
   self-contained trace for the desired exports
3. **Replay**: merged trace replayed from scratch in a bare kernel
   session (`bin/hol --min`) to verify exports are oracle-free

## Trace Format (`.pft`)

### Grammar

```
trace        ::= version entry* name? exports
version      ::= "V " int "\n"
entry        ::= type_entry | term_entry | thm_entry | compute_init
name         ::= "N " s "\n"
exports      ::= ("E " s p "\n")*

type_entry   ::= "Y " y " V " s "\n"
               | "Y " y " O " s s y* "\n"

term_entry   ::= "T " t " V " s y "\n"
               | "T " t " C " s s y "\n"
               | "T " t " A " t t "\n"
               | "T " t " L " t t "\n"

thm_entry    ::= "P " p " " rule args "\n"

compute_init ::= "C " y y (s t){29} (s p)* "\n"
```

Fields:
- **y**: type ID (non-negative integer)
- **t**: term ID (non-negative integer)
- **p**: theorem ID (non-negative integer)
- **s**: unquoted token or quoted string (`"..."` with `\"`, `\\`,
  `\n`, `\xNN` escapes)
- IDs are scoped per namespace (Y, T, P)
- Y, T, P, C entries are interleaved in dependency order
- V is the first line; N and E entries appear at the end
- N is optional (absent in merged traces)

The `C` entry records initialization arguments for `Thm.compute`.
At most once per trace, before any COMPUTE theorems. Arguments:
cval_type (y), num_type (y), 29 cval (name, term) pairs, then
char_eqn (name, parent) pairs until end of line.

### Theorem Rules

Each `P` entry constructs a theorem. Variable-length arguments
extend to end of line.

| Rule | Arguments |
|------|-----------|
| `REFL` | `t` |
| `ASSUME` | `t` |
| `BETA_CONV` | `t` |
| `ALPHA` | `t t` |
| `ABS` | `p t` |
| `MK_COMB` | `p p` |
| `AP_TERM` | `p t` |
| `AP_THM` | `p t` |
| `SYM` | `p` |
| `TRANS` | `p p` |
| `EQ_MP` | `p p` |
| `EQ_IMP_RULE1` | `p` |
| `EQ_IMP_RULE2` | `p` |
| `MP` | `p p` |
| `DISCH` | `p t` |
| `INST_TYPE` | `p (y y)*` |
| `INST` | `p (t t)*` |
| `SUBST` | `p t (t p)*` — original, template, (var, residue) pairs |
| `SPEC` | `p t` |
| `Specialize` | `p t` — lazy-beta SPEC |
| `GEN` | `p t` |
| `GENL` | `p t*` |
| `GEN_ABS` | `p t t*` — parent, opt_cst (`~` for NONE), vars |
| `EXISTS` | `p t t` — parent, existential, witness |
| `CHOOSE` | `p p t` |
| `CONJ` | `p p` |
| `CONJUNCT1` | `p` |
| `CONJUNCT2` | `p` |
| `DISJ1` | `p t` |
| `DISJ2` | `p t` |
| `DISJ_CASES` | `p p p` |
| `NOT_INTRO` | `p` |
| `NOT_ELIM` | `p` |
| `CCONTR` | `p t` |
| `Beta` | `p` — compute-optimized right-beta |
| `Mk_comb` | `p p p` — original, fun result, arg result |
| `Mk_abs` | `p p` — original, body result |
| `DEF_TYOP` | `p s s` — witness, thy, tyop |
| `DEF_SPEC` | `p s s*` — witness, thyname, cnames |
| `COMPUTE` | `t p*` — input term, code equation parents |
| `AXIOM` | `t` |
| `ORACLE` | `s t t*` — tag, concl, hyps |
| `DISK_THM` | `s s` — theory, name (per-theory only) |

## Recording

`TraceRecord` sets `Thm.trace_hook` to intercept every kernel
inference rule. On each call:

1. Interns new types/terms, writing Y/T entries to the output
   stream immediately
2. Resolves parent theorem references to file theorem IDs via
   `id_to_line` map. Heap theorems (not in map) trigger a
   DISK_THM entry on demand.
3. Writes the P entry (or C for COMPUTE_INIT)

The output stream is opened on the first write, piped through a
compressor (zstd > gzip > uncompressed) to a temporary file.
The V line is written first.

In-memory state:
- `ty_map`, `tm_map`: structural dedup maps (type/term → ID)
- `id_to_line`: kernel trace_id → file theorem ID
- `lines_written`: next theorem ID counter

At `export_theory()` time, the export hook appends N and E entries,
closes the compressor, renames the temp file to
`<thyname>Theory.pft.zst`, and resets state.

Per-theory traces include all steps recorded during the process,
including library loading. No filtering is done — the merge tool
handles that.

## Merge Tool

Input: list of per-theory `.pft` file paths, plus desired
exports `(theory, name)`.

Output: single self-contained `.pft` with only entries
reachable from the desired exports, types/terms globally
deduplicated, DISK_THM resolved. No N line.

### Pass 1: Determine what's needed

Starting from the desired exports, work backward to discover all
needed theorems, terms, types, and ancestor theories.

For each theory (starting with theories containing desired exports,
loading ancestors on demand as they are discovered):

1. Stream through the trace file, building a dependency graph:
   for each P entry, record which P/T/Y IDs it references
   (per-rule parsing of arguments); for each T entry, record
   which T/Y IDs it references; for each Y entry, record which
   Y IDs it references. Also record E and DISK_THM entries.
   Full line text is not stored — only dependency lists.
2. Walk backward from the needed theorem IDs, marking live P
   entries, then transitively marking the T and Y entries they
   reference as live.
3. When the walk hits a DISK_THM entry (thy, name), add that to
   the needed ancestor exports. If the ancestor's trace hasn't
   been processed yet, process it (step 1-3).
4. Store the set of live entry IDs for this theory (a compact
   bit set). Discard the dependency graph.

Each theory is streamed once in this pass. Memory per theory is
proportional to the number of entries × average dependencies per
entry (a few ints each), not the full file content. After the
pass completes, we have live entry ID sets per theory and a
topological ordering of the needed theories.

### Pass 2: Write merged trace

Re-read each needed theory's trace in dependency order, writing
only live entries to the output with globally remapped IDs.

Persistent state:
- Global type dedup map: `type_descriptor → global_type_id`
- Global term dedup map: `term_descriptor → global_term_id`
- Ancestor export map: `(theory, name) → global_theorem_id`

Type descriptors: `(V, name)` or `(O, thy, name, [global_arg_ids])`.
Term descriptors: `(V, name, global_tyid)`,
`(C, thy, name, global_tyid)`, `(A, global_fid, global_xid)`,
`(L, global_vid, global_bid)`.

Per-theory (discarded after each):
- Local-to-global remap arrays for types, terms, theorems

For each theory's live entries:
- **Y**: dedup via type descriptor. Write if new, remap if existing.
- **T**: dedup via term descriptor. Write if new, remap if existing.
- **P DISK_THM**: resolve via ancestor export map, record
  local→global mapping (no output).
- **P (other)**: remap all argument IDs, assign new global theorem
  ID, write.
- **C**: remap and write.

After each theory: register its live exports in the ancestor export
map.

After all theories: write E lines for desired exports.

### Theorem dedup

Currently not performed — each non-DISK_THM P entry gets a fresh
global ID. Possible future approaches:

1. **Derivation-based**: dedup P entries with identical remapped
   arguments. Low overhead but incomplete.
2. **Statement-based**: record theorem statements in traces for
   full structural dedup. Increases trace size.

Pending empirical data from large merges.

### Complexity

- Each needed theory file read twice (pass 1 + pass 2)
- Per-theory work: linear in entries
- Global maps: O(log N) per lookup
- Memory: global term dedup map dominates (~40 bytes/unique term).
  For HOL's 12.5M total terms: ~240MB estimated.

## Replay

A merged trace is replayed from scratch in `bin/hol --min` (only
min theory loaded) in a single forward pass. Three ID-indexed
arrays map type, term, and theorem IDs to their constructed
objects:

- **Y entries**: construct the type, store in type array
- **T entries**: construct the term (looking up sub-component
  types/terms from the arrays), store in term array
- **P entries**: call the corresponding kernel inference rule
  (looking up argument types/terms/theorems from the arrays),
  store the resulting theorem in the theorem array
- **C entry**: call `Thm.compute` with the init args, save
  the closure for subsequent COMPUTE entries
- **E entries**: look up the theorem, verify it is oracle-free

Since the merged trace is in dependency order, each entry's
dependencies have already been constructed. No lazy construction
is needed (unlike per-theory replay where definitions may
interleave with term construction).

### Memory management

Without GC, replay must keep all constructed objects alive for
the duration. For large traces this can be significant (e.g.,
25M theorems at ~200 bytes each ≈ 5GB). Two strategies for
reducing peak memory:

1. **Replay-side last-reference pass**: Before replaying, do a
   quick linear scan of the trace to compute, for each entry,
   the ID of the last entry that references it. During replay,
   null out array entries after their last reference. This adds
   one integer per entry of overhead and one extra linear pass.

2. **Merge-side entry ordering**: The merge tool could optionally
   reorder entries (within the constraints of dependency order)
   to minimize the maximum live set, reducing peak memory
   without any replay-side changes. This is a scheduling
   optimization in the merge tool's pass 2.

Both are optional future optimizations. The initial
implementation keeps all objects alive.

## Compression

Files may be `.pft.zst` (preferred), `.pft.gz`, or
uncompressed `.pft`. Auto-detected from extension.
