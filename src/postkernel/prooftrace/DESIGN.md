# HOL4 Proof Trace System

## Overview

The proof trace system records kernel inference steps during HOL4
builds and produces trace files that can be merged and replayed
from scratch for independent verification.

The pipeline has three stages:
1. **Recording**: `.pft` files produced during `--trace` builds
   (one per theory, one per heap)
2. **Merging**: per-theory and heap traces combined into a single
   self-contained trace for the desired exports
3. **Replay**: merged trace replayed from scratch in a bare kernel
   session (`bin/hol --min`) to verify exports are oracle-free

## Enabling tracing

- `bin/build --trace` for HOL sources
- `Holmake --trace` for external projects

The `--trace` flag on build passes `--trace` to each Holmake
invocation. Holmake `--trace` propagates `HOL_TRACE_PROOFS=1`
as an environment variable to all child processes (via shell
command prefix, same mechanism as `relocbuild`). TraceRecord
checks this env var at load time and activates if set.

## Trace Format (`.pft`)

### Grammar

```
trace        ::= version heap? entry* name? exports
version      ::= "V " int "\n"
heap         ::= "H " s "\n"
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
- **y**: type ID (non-negative integer, sequential from 0)
- **t**: term ID (non-negative integer, sequential from 0)
- **p**: theorem ID (kernel trace_id — see below)
- **s**: unquoted token or quoted string (`"..."` with `\"`, `\\`,
  `\n`, `\xNN` escapes)
- IDs are scoped per namespace (Y, T, P)
- Y, T, P, C entries are interleaved in dependency order
  (as recorded during the build)
- V is the first line; H (if present) is second; N and E entries
  appear at the end
- H records the absolute filesystem path of the parent heap this
  trace was built on (e.g., `/home/user/HOL/bin/hol.state0`).
  This is the value of the `--holstate` or `-b` argument passed
  to the process. Omitted if there is no parent heap (e.g., the
  initial heap build). The merge tool locates the parent heap's
  trace file at `<H_path>.pft`.

### Theorem ID uniqueness

Theorem IDs (`p`) are kernel `Thm.trace_id` values from a
monotonic per-process counter. The counter is saved and restored
with heaps. This gives the following properties:

- Within a single process (one theory script or one heap build),
  trace_ids are unique and monotonically increasing.
- Heaps form a linear ancestry chain: `hol.state0` assigns
  trace_ids [0, N], `numheap` (built on top of `hol.state0`)
  continues from N+1 to M, etc. Each heap build's trace_ids
  are disjoint from its ancestors'.
- Parallel theory scripts loading the same heap start from the
  same counter value and have overlapping trace_id ranges. But
  parallel scripts never reference each other's theorems — they
  only reference the heap chain's theorems (via parent trace_ids)
  and ancestor theories (via DISK_THM by name).

Therefore: within the heap chain that a theory depends on,
trace_ids are globally unique. The merge tool can resolve a
parent trace_id not found in the current file by searching the
heap chain's `.pft` files without ambiguity.

### Trace file types

**Theory traces** (`<thy>Theory.pft[.zst|.gz]` in `.hol/objs/`):
contain all steps recorded during a theory script, including
library loading. Have N (theory name) and E (export) lines at
the end. DISK_THM entries reference ancestor theorems by
`(theory, name)`.

**Heap traces** (`<heapname>.pft[.zst|.gz]` alongside the heap
file): contain all steps recorded during heap building. No N
or E lines. Steps include library initialization, type base
setup, simpset construction, etc. Compressed on exit using the
same preference as theory traces (zstd > gzip > uncompressed).

**Merged traces** (user-specified path): a single self-contained
trace produced by the merge tool. No N line. Has E lines for
the desired exports. No DISK_THM entries (all resolved). Types
and terms globally deduplicated.

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
| `AXIOM` | `s t` — axiom name, conclusion |
| `ORACLE` | `s t t*` — tag, concl, hyps |
| `DISK_THM` | `s s` — theory, name (per-theory traces only) |

The `C` entry records initialization arguments for `Thm.compute`.
At most once per trace, before any COMPUTE theorems. Arguments:
cval_type (y), num_type (y), 29 cval (name, term) pairs, then
char_eqn (name, parent) pairs until end of line.

## Recording

TraceRecord is always loaded into `hol.state0` (first in UOARGS,
before other libraries). At load time it checks `OS.Process.getEnv
"HOL_TRACE_PROOFS"` and activates if set.

### Activation

`activate()` sets `Thm.trace_hook` and `Thm.trace_export_hook`,
and registers an `atExit` cleanup handler. When not activated
(no env var), hooks remain NONE — zero overhead.

### Output file selection

At activation time, TraceRecord parses `CommandLine.arguments()`
for `-o <path>`. If found, this is a heap build — the trace is
written directly to `<path>.pft`. If not found, this is a theory
script — the trace is written to a temp file (renamed at export
time).

### Recording steps

On each kernel inference rule:
1. Intern new types/terms, writing Y/T entries to the output
   immediately
2. Write the P entry with kernel trace_ids for both the entry's
   own ID and parent references — no remapping

P entry IDs are `Thm.trace_id` values from the kernel's monotonic
counter. Parent references are also `Thm.trace_id` values of the
parent thm values. No `id_to_line` mapping is needed.

For `TR_DISK_THM` (theorem loaded from a `.dat` file), the entry
is `P <trace_id> DISK_THM <theory> <name>`.

### Stale stream handling

When a process loads a saved heap, TraceRecord's output stream
is stale (from the heap build's session). On first write attempt,
the stale stream is detected and a new output is opened:
- If `-o <path>` is in the command line args → heap build,
  open `<path>.pft`
- Otherwise → theory script, open a temp file

The intern tables (ty_map, tm_map) are reset for the new session.
Type/term IDs restart from 0.

### Theory export

At `export_theory()` time, `Thm.trace_export` fires the export
hook which:
1. Closes the temp file
2. Appends N and E lines
3. Compresses (zstd > gzip > uncompressed) and writes to
   `.hol/objs/<thyname>Theory.pft[.zst|.gz]`
4. Removes the temp file
5. Resets recording state

### Heap export

For heap builds, there is no `export_theory()` call. The trace
file is written directly from the start. The `atExit` handler
closes the stream, compresses the file (zstd > gzip >
uncompressed, same preference as theory traces), and writes
the final output to `<heapname>.pft[.zst|.gz]`. No N or E
lines are written.

## Merge Tool

Input: list of `.pft` file paths (theory traces and heap traces),
plus desired exports `(theory, name)`.

Output: single self-contained `.pft` with only entries reachable
from the desired exports, types/terms globally deduplicated, all
DISK_THM and cross-file references resolved. No N line.

### Pass 1: Determine what's needed

Starting from the desired exports, work backward to discover all
needed theorems, terms, types, and ancestor theories/heaps.

For each trace file (starting with files containing desired
exports, loading ancestors on demand as discovered):

1. Stream through the trace file, building a dependency graph:
   for each P entry, record which P/T/Y IDs it references
   (per-rule parsing of arguments); for each T entry, record
   which T/Y IDs it references; for each Y entry, record which
   Y IDs it references. Also record E and DISK_THM entries.
   Full line text is not stored — only dependency lists.
2. Walk backward from the needed theorem IDs, marking live P
   entries, then transitively marking the T and Y entries they
   reference as live. When a T entry for a non-primitive
   constant (`C thy name tyid` where thy ≠ `min`) is marked
   live, the DEF_SPEC that defines that constant (if present
   in this file) is also marked live. Similarly, when a Y
   entry for a non-primitive type operator is marked live, the
   corresponding DEF_TYOP is marked live. This cascades
   naturally within the reachability walk.
3. When the walk hits a DISK_THM entry (thy, name), add that
   to the needed ancestor exports. If the ancestor's trace
   hasn't been processed yet, process it.
4. When the walk hits a parent trace_id not in the current file,
   follow the H (heap) line to find the parent heap's `.pft`
   file, and search up the heap ancestry chain for a P entry
   with that trace_id. If found, process that heap trace and
   mark the needed entries. If not found in any ancestor heap,
   this is a hard error (indicates a recording bug or missing
   heap trace file).
5. Store the set of live entry IDs for this file (compact bit
   set). Discard the dependency graph.

### Pass 2: Write merged trace

Re-read each needed trace file in dependency order, writing
only live entries to the output with globally remapped IDs.

Dependency order is determined by a unified topological sort
across all files (both heap and theory traces). A file depends
on another if:
- It has a live DISK_THM referencing a theory → depends on
  that theory's trace file
- It has an H line pointing to a parent heap → depends on
  that heap's trace file

Note that heap traces can contain DISK_THM entries (e.g.,
`hol.state0` loads `boolTheory` from disk), so theory traces
may need to be written before the heap traces that reference
them.

Persistent state:
- Global type dedup map: `type_descriptor → global_type_id`
- Global term dedup map: `term_descriptor → global_term_id`
- Ancestor export map: `(theory, name) → global_theorem_id`
- Heap theorem map: `(file, trace_id) → global_theorem_id`

Type descriptors: `(V, name)` or `(O, thy, name, [global_arg_ids])`.
Term descriptors: `(V, name, global_tyid)`,
`(C, thy, name, global_tyid)`, `(A, global_fid, global_xid)`,
`(L, global_vid, global_bid)`.

Per-file (discarded after each):
- Local-to-global remap arrays for types, terms, theorems

For each file's live entries:
- **Y**: dedup via type descriptor. Write if new, remap if existing.
- **T**: dedup via term descriptor. Write if new, remap if existing.
- **P DISK_THM**: resolve via ancestor export map, record
  local→global mapping (no output).
- **P (other)**: remap all argument IDs, assign new global theorem
  ID, write.
- **C**: remap and write.

After each file: register its exports (if any) in the ancestor
export map. Register its P entries in the heap theorem map (if
it's a heap trace).

After all files: write E lines for desired exports.

### Theorem dedup

Currently not performed — each non-DISK_THM P entry gets a fresh
global ID. Possible future approaches:

1. **Derivation-based**: dedup P entries with identical remapped
   arguments. Low overhead but incomplete.
2. **Statement-based**: record theorem statements in traces for
   full structural dedup. Increases trace size.

Pending empirical data from large merges.

### Complexity

- Each needed file read twice (pass 1 + pass 2)
- Per-file work: linear in entries
- Global maps: O(log N) per lookup
- Memory: global term dedup map dominates (~40 bytes/unique term).
  For HOL's 12.5M total terms: ~240MB estimated.

## Replay

A merged trace is replayed from scratch in `bin/hol --min` (only
min theory loaded) in a single forward pass.

Types and terms are constructed **lazily**: Y and T entries store
raw descriptions when first encountered. Actual type/term values
are constructed on demand when first referenced by a P entry.
This ensures definitions (DEF_TYOP, DEF_SPEC) are replayed before
the types and terms they define are constructed, avoiding stale
kernelid issues.

Theorems are stored in a map keyed by trace_id (which can be
large/sparse, unlike sequential type/term IDs).

- **Y entries**: store type description (constructed lazily)
- **T entries**: store term description (constructed lazily)
- **P entries**: call the corresponding kernel inference rule
  (triggering lazy construction of any referenced types/terms),
  store the resulting theorem in the theorem map
- **C entry**: call `Thm.compute` with the init args, save
  the closure for subsequent COMPUTE entries
- **E entries**: look up the theorem, verify it is oracle-free

### Memory management

Without GC, replay must keep all constructed objects alive for
the duration. For large traces this can be significant (e.g.,
25M theorems at ~200 bytes each ≈ 5GB). Two strategies for
reducing peak memory:

1. **Replay-side last-reference pass**: Before replaying, do a
   quick linear scan of the trace to compute, for each entry,
   the ID of the last entry that references it. During replay,
   null out entries after their last reference. This adds one
   integer per entry of overhead and one extra linear pass.

2. **Merge-side entry ordering**: The merge tool could optionally
   reorder entries (within the constraints of dependency order)
   to minimize the maximum live set, reducing peak memory
   without any replay-side changes.

Both are optional future optimizations. The initial
implementation keeps all objects alive.

## Compression

Files may be `.pft.zst` (preferred), `.pft.gz`, or
uncompressed `.pft`. Auto-detected from extension.
