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
trace        ::= version heap? entry* name? provenance? exports
version      ::= "V " int "\n"
heap         ::= "H " s "\n"
entry        ::= type_entry | term_entry | thm_entry
               | const_decl | type_decl | compute_init
name         ::= "N " s "\n"
provenance   ::= (named_prov | anon_prov)*
named_prov   ::= "F " s s p "\n"
anon_prov    ::= "G " s int p "\n"
exports      ::= ("E " s p "\n")*

const_decl   ::= "C " s s y "\n"
type_decl    ::= "O " s s int "\n"

type_entry   ::= "Y " y " V " s "\n"
               | "Y " y " O " s s y* "\n"

term_entry   ::= "T " t " V " s y "\n"
               | "T " t " C " s s y "\n"
               | "T " t " A " t t "\n"
               | "T " t " L " t t "\n"

thm_entry    ::= "P " p " " rule args "\n"

compute_init ::= "I " y y (s t){29} (s p)* "\n"
```

Fields:
- **y**: type ID (non-negative integer, sequential from 0)
- **t**: term ID (non-negative integer, sequential from 0)
- **p**: theorem ID (kernel trace_id — see below)
- **s**: unquoted token or quoted string (`"..."` with `\"`, `\\`,
  `\n`, `\xNN` escapes)
- IDs are scoped per namespace (Y, T, P)
- Y, T, P, I entries are interleaved in dependency order
  (as recorded during the build)
- V is the first line; H (if present) is second; C, O, Y, T,
  P, and I entries are interleaved in dependency order; N
  appears after all entries; F and G (provenance, merged traces
  only) appear after N; E entries appear last
- H records the absolute filesystem path of the parent heap this
  trace was built on (e.g., `/home/user/HOL/bin/hol.state0`).
  This is the value of the `--holstate` or `-b` argument passed
  to the process. Omitted if there is no parent heap (e.g., the
  initial heap build). The merge tool locates the parent heap's
  trace file at `<H_path>.pft`.

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
| `REFL_RATOR` | `p` — REFL of rator(rhs(concl parent)), from Mk\_comb |
| `REFL_RAND` | `p` — REFL of rand(rhs(concl parent)), from Mk\_comb |
| `REFL_BODY` | `p` — REFL of body(rhs(concl parent)), from Mk\_abs |
| `Mk_comb` | `p p p` — original, fun result, arg result |
| `Mk_abs` | `p p` — original, body result |
| `DEF_TYOP` | `p s s` — witness, thy, tyop |
| `DEF_SPEC` | `p s s*` — witness, thyname, cnames |
| `COMPUTE` | `t p*` — input term, code equation parents |
| `AXIOM` | `s t` — axiom name, conclusion |
| `ORACLE` | `s t t*` — tag, concl, hyps |
| `NAME` | `s s` — theory, name (per-theory traces only) |
| `LOAD` | `s p` — theory, ancestor trace_id (per-theory traces only) |

**REFL\_RATOR / REFL\_RAND / REFL\_BODY**: `Mk_comb` and `Mk_abs`
internally produce REFL theorems for the sub-terms of the parent's
RHS. These lightweight trace steps reference only the parent
theorem (no term interning), and replay reconstructs the term via
`dest_comb`/`dest_abs` on the parent's RHS. This avoids O(term\_size)
interning on the EVAL hot path, where every `Mk_comb` step would
otherwise intern potentially large intermediate terms.

### Constant and Type Declarations

`C thy name ty_id` — declares a constant introduced by
`new_constant` (or equivalent) that has no associated definition
theorem. `thy` and `name` identify the constant; `ty_id`
references a Y entry for the constant's (polymorphic) type.

`O thy name arity` — declares a type operator introduced by
`new_type` (or equivalent) that has no associated definition
theorem. `thy` and `name` identify the type operator; `arity`
is a non-negative integer.

**Trace-time filtering**: Constants introduced by
`new_definition`, `new_specification`, etc. already have a
DEF_SPEC P entry that introduces them as a side effect. To
avoid redundancy, TraceRecord tracks which constants have been
introduced via DEF_SPEC and which types via DEF_TYOP; C/O
lines are only emitted for constants/types that have no
corresponding definition. This is possible because
`TheoryDelta.NewConstant`/`NewTypeOp` always fires after the
definition's `Thm.save` (which emits the DEF_SPEC/DEF_TYOP P
line), so the set is up-to-date when the hook fires.

Each constant/type in a trace has exactly one of:
- A DEF_SPEC/DEF_TYOP P entry (introduced by a definition), or
- A C/O declaration (introduced by `new_constant`/`new_type`)

The `I` entry records initialization arguments for `Thm.compute`.
At most once per trace, before any COMPUTE theorems. Arguments:
cval_type (y), num_type (y), 29 cval (name, term) pairs, then
char_eqn (name, parent) pairs until end of line.

### Provenance Lines (merged traces only)

`F thy name global_id` — records that the P entry with
`global_id` is a named export called `name` from theory `thy`.
Emitted for every named export (E line) from every theory
included in the merge, not just the desired exports.

`G thy src_trace_id global_id` — records that the P entry with
`global_id` is the theorem that had `src_trace_id` in theory
`thy`'s build process. Emitted for every LOAD reference
resolved during the merge.

These lines are only present in merged traces and are consumed
by `--interactive` replay to map replayed theorems back to
their theory origins (see Replay-aware Theory Loading below).
Per-theory and heap traces do not have F or G lines.

### Theorem ID uniqueness

Theorem IDs (`p`) are kernel `Thm.trace_id` values from a
monotonic per-process counter. The counter is saved and restored
with heaps.

**Within a theory trace**: trace_ids are unique. Each theory
script is a single process, so its trace_ids are monotonically
increasing. Sibling theories (e.g., A and B both built on the
same heap) may have overlapping trace_id ranges, but this is
harmless because cross-file references to theory theorems
always carry the theory name (via NAME or LOAD).

**Within the heap chain**: trace_ids are globally unique across
all heaps in the chain. Heaps form a linear ancestry:
`hol.state0` assigns trace_ids [0, N], `numheap` (built on
`hol.state0`) continues from N+1 to M, etc. Each heap's
trace_ids are disjoint from its ancestors'. Theory scripts
inherit their heap's counter, so theory trace_ids also do not
overlap with any heap in their ancestry chain.

**Cross-file theorem references** come in three forms:

- **Named** (`NAME thy name`): references a named theory export
  by theory and name. Resolved via E lines in the ancestor
  theory's trace.
- **Anonymous** (`LOAD thy trace_id`): references an anonymous
  theorem (e.g., thydata-embedded) by theory name and trace_id.
  Both the theory name and trace_id are stored together in the
  `.dat` file alongside the theorem data: the theory name is
  `Theory.current_theory()` at write time, and the trace_id is
  the theorem's `Thm.trace_id` in the writing process. This
  ensures they always refer to the same trace file, even when
  the theorem was originally created in a different theory and
  re-exported through thydata. Since LOAD always carries the
  theory name, there is no ambiguity between sibling theories
  with overlapping trace_id ranges. Resolved by finding the
  P entry with that trace_id in the named theory's trace.
- **Heap parent**: a parent trace_id in a P entry that is not
  found in the current file. This must be in the heap ancestry
  chain, where trace_ids are globally unique. Resolved by
  searching up the heap chain for a P entry with that trace_id.

### Trace file types

**Theory traces** (`<thy>Theory.pft` in `.hol/objs/`):
contain all steps recorded during a theory script, including
library loading. Have N (theory name) and E (named export)
lines at the end. NAME entries reference named ancestor
theorems by `(theory, name)`. LOAD entries reference anonymous
ancestor theorems (including thydata-embedded theorems such as
simpset rewrites and TypeBase data) by `(theory, trace_id)`,
both stored in the `.dat` file by the exporting theory.

**Heap traces** (`<heapname>.pft` alongside the heap file):
contain all steps recorded during heap building. No N or E
lines. Steps include library initialization, type base setup,
simpset construction, etc.

**Merged traces** (user-specified path): a single self-contained
trace produced by the merge tool. No N line. Has E lines for
the desired exports. No NAME or LOAD entries (all resolved).
Types and terms globally deduplicated. Has F and G provenance
lines mapping replayed theorems to their theory-level origins
(for use by replay-aware theory loading).

## Recording

TraceRecord is always loaded into `hol.state0` (first in UOARGS,
before other libraries). At load time it checks `OS.Process.getEnv
"HOL_TRACE_PROOFS"` and activates if set.

### Activation

`activate()` sets `Thm.trace_hook` and `Thm.trace_export_hook`,
registers a `Theory.register_hook` for `NewConstant`/`NewTypeOp`
TheoryDelta events (to emit C/O lines), and registers an
`atExit` cleanup handler. When not activated (no env var), hooks
remain NONE — zero overhead.

### Output file selection

At activation time, TraceRecord parses `CommandLine.arguments()`
for `-o <path>`. If found, this is a heap build — the trace is
written directly to `<path>.pft`. If not found, this is a theory
script — the trace is written to a temp file under `.hol/objs/`
(renamed at export time).

### Recording steps

On each kernel inference rule:
1. Intern new types/terms, writing Y/T entries to the output
   immediately
2. Write the P entry with kernel trace_ids for both the entry's
   own ID and parent references — no remapping

P entry IDs are `Thm.trace_id` values from the kernel's monotonic
counter. Parent references are also `Thm.trace_id` values of the
parent thm values.

There are two kinds of theorems loaded from `.dat` files:

**Named exports** are loaded via `SharingTables.read_thm`, which
knows the theorem's name. These are recorded as
`P <trace_id> NAME <theory> <name>`.

**Anonymous theorems** (thydata-embedded theorems used by
simpsets, TypeBase, etc.) are loaded via `ThyDataSexp.thmreader`.
The `.dat` file stores both the source theory name
(`Theory.current_theory()` at write time) and the theorem's
trace_id from that process. These are recorded as
`P <trace_id> LOAD <source_theory> <source_trace_id>`.

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
1. Closes the recording output stream
2. Reopens the temp file in append mode, writes N and E lines
3. Renames to `.hol/objs/<thyname>Theory.pft`
4. Resets recording state

E lines map named exports to trace_ids.

Anonymous theorems do not need export lines. Their source
theory name and trace_id are stored in the `.dat` file at
serialization time, so descendant traces can reference them
directly using LOAD entries.

### Heap export

For heap builds, there is no `export_theory()` call. The trace
file (`<heapname>.pft`) is written directly from the start and
closed by the `atExit` handler when the process exits. No N or
E lines are written.

## Merge Tool

Input: list of `.pft` file paths (theory traces and heap traces),
plus desired exports `(theory, name)`.

Output: single self-contained `.pft` with only entries reachable
from the desired exports, types/terms globally deduplicated, all
NAME and LOAD cross-file references resolved. No N line.

### Pass 1: Determine what's needed

Starting from the desired exports, work backward to discover all
needed theorems, terms, types, and ancestor theories/heaps.

For each trace file (starting with files containing desired
exports, loading ancestors on demand as discovered):

1. Stream through the trace file, building lightweight metadata:
   for each Y entry, record sub-type dependencies; for each T
   entry, record sub-term and sub-type dependencies; for each P
   entry, record only its byte offset in the file (not its
   dependencies — those are read lazily). Also record E, NAME,
   LOAD, DEF_SPEC, DEF_TYOP, C, and O entries. A Posix file
   descriptor is kept open for random-access seeking to P entry
   byte offsets during the reachability walk.
2. Walk backward from the needed theorem IDs, marking live P
   entries, then transitively marking the T and Y entries they
   reference as live. When a T entry for a non-primitive
   constant (`C thy name tyid` where thy ≠ `min`) is marked
   live, the definition or declaration that introduces that
   constant is also marked live. Specifically: if a DEF_SPEC
   exists for the constant (in this file or an ancestor
   theory's trace), it is marked live; otherwise, if a C
   declaration exists, it is marked live. Similarly for types:
   DEF_TYOP if it exists, otherwise O. When the definition
   or declaration is in an ancestor theory's trace file, that
   file is loaded and the entry is enqueued for processing
   (analogous to NAME resolution). This cascades naturally
   within the reachability walk. C lines also mark their
   referenced type as live.
3. When the walk hits a NAME entry (thy, name), add that
   to the needed ancestor exports (resolved via E lines). When
   it hits a LOAD entry (thy, trace_id), find the P entry with
   that trace_id in the ancestor theory's trace and mark it
   live. If the ancestor's trace hasn't been processed yet,
   process it.
4. When the walk hits a parent trace_id not in the current file,
   follow the H (heap) line to find the parent heap's `.pft`
   file, and search up the heap ancestry chain for a P entry
   with that trace_id. If found, process that heap trace and
   mark the needed entries. If not found in any ancestor heap,
   this is a hard error (indicates a recording bug or missing
   heap trace file).
5. Store the set of live entry IDs for this file (bit arrays
   for Y/T, int map for P). After Pass 1 completes for all
   files, close the Posix fds and discard the per-file
   dependency metadata.

### Pass 2: Write merged trace

Re-read each needed trace file in dependency order, writing
only live entries to the output with globally remapped IDs.

Dependency order is determined by a unified topological sort
across all files (both heap and theory traces). A file depends
on another if:
- It has a live NAME or LOAD referencing a theory →
  depends on that theory's trace file
- It has an H line pointing to a parent heap → depends on
  that heap's trace file

Note that heap traces can contain NAME/LOAD entries (e.g.,
`hol.state0` loads `boolTheory` from disk), so theory traces
may need to be written before the heap traces that reference
them.

Persistent state:
- Global type dedup map: `type_descriptor → global_type_id`
- Global term dedup map: `term_descriptor → global_term_id`
- Ancestor export map: `(theory, name) → global_theorem_id`
- Ancestor theorem map: `(theory, trace_id) → global_theorem_id`
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
- **C**: remap type ID, write. (Dedup not needed — each
  constant has at most one C across all files.)
- **O**: write as-is. (Dedup not needed — each type operator
  has at most one O across all files.)
- **P NAME**: resolve via ancestor export map, record
  local→global mapping (no output).
- **P LOAD**: resolve via ancestor theorem map, record
  local→global mapping (no output).
- **P (other)**: remap all argument IDs, assign new global theorem
  ID, write.
- **I**: remap and write if any COMPUTE P entry is live (across
  all files). The I line may be in a different file (typically a
  heap trace) from the COMPUTE entries that depend on it. When
  the first COMPUTE entry is marked live in Pass 1, the I line's
  file is found (by walking up the heap chain), and the I line's
  char_eqn parent thm IDs and cval term/type refs are marked
  live.

After each file: register its E exports (if any) in the ancestor
export map. Emit F lines for each named export that was mapped
to a global ID. Register its P entries in the ancestor theorem
map (for theory traces) or the heap theorem map (for heap
traces).

During LOAD resolution: when a LOAD is successfully resolved
to a global ID, emit a G line recording the `(src_thy,
src_trace_id, global_id)` mapping.

After all files: write E lines for desired exports.

### Theorem dedup

Currently not performed — each non-NAME/LOAD P entry gets a fresh
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
- **C entries**: call `Term.prim_new_const {Thy, Name} ty` to
  declare the constant in the kernel
- **O entries**: call `Type.prim_new_type {Thy, Name} arity` (or
  equivalent) to declare the type operator in the kernel
- **P entries**: call the corresponding kernel inference rule
  (triggering lazy construction of any referenced types/terms),
  store the resulting theorem in the theorem map
- **I entry**: call `Thm.compute` with the init args, save
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

## Replay-aware Theory Loading

After replaying a merged trace, the kernel contains types,
constants, and theorems established by genuine inference rules.
To use the session interactively (pretty-printing, simplification,
etc.), the theory hierarchy must be loaded: `Theory.link_parents`,
`DB.bindl`, simpsets, TypeBase, grammars, and other thydata must
be populated.

The normal loading path (`TheoryReader.load_thydata`) reads `.dat`
files and reconstructs theorems via `Thm.disk_thm`, producing
DISK_THM oracles. After replay, we want to substitute replayed
theorem values wherever available, falling back to DISK_THM
creation for theorems not included in the merge.

### Provenance from the merge tool

The merge tool emits **F** and **G** provenance lines in the
merged trace (see Provenance Lines above):

- `F thy name global_id` — for every named export from every
  included theory
- `G thy src_trace_id global_id` — for every resolved LOAD
  reference

These lines record the mapping from theory-level identifiers
(used by `.dat` files) to global IDs in the merged trace
(used by the replayer's theorem map).

### Building replay maps

After replay, the replayer has a theorem map
`global_id → thm` for every P entry. Using the provenance
lines, it builds two lookup maps:

- **Named replay map**: `(theory, name) → thm` — built from
  F lines by looking up each `global_id` in the theorem map
- **Anonymous replay map**: `(theory, trace_id) → thm` — built
  from G lines similarly

These maps are the interface between replay and theory loading.

### Substitution during theory loading

The replay maps are installed as a single optional ref in the
`Thm` structure (accessible to both `SharingTables` and
`ThyDataSexp`):

```sml
val replay_thms :
  { named : (string * string, thm) map,
    anon  : (string * int, thm) map } option ref
```

When set, the theorem creation functions check these maps
first:

- **`disk_thm (Named(thy, name)) ((dd,ocl), terms)`**: looks
  up `(thy, name)` in `#named`. If found, returns the replayed
  theorem. Otherwise creates a DISK_THM as normal.

- **`disk_thm (Anon(thy, trace_id)) ((dd,ocl), terms)`**:
  looks up `(thy, trace_id)` in `#anon`. If found, returns the
  replayed theorem. Otherwise creates a DISK_THM as normal.

When not set (normal non-replay loading), behaviour is
unchanged — zero overhead.

### Handling types and constants

After replay, types and constants are already in the kernel
(created by DEF_TYOP, DEF_SPEC, C, and O entries during
replay). The normal `incorporate_types` / `incorporate_consts`
calls in `load_thydata` would re-register them via
`prim_new_type` / `prim_new_const`, which retires the
existing kernelid and creates a new one — invalidating all
replayed terms and theorems that reference the old kernelid.

To prevent this, `incorporate_types` and `incorporate_consts`
must skip types and constants that already exist in the
kernel with matching identity. Specifically:

- **Types**: if `Type.op_arity {Thy, Tyop}` returns
  `SOME arity` matching the expected arity, skip.
- **Constants**: if `Term.prim_mk_const {Thy, Name}` succeeds
  (the constant exists), skip. (Type instantiation means the
  stored type in the `.dat` file may differ from the
  polymorphic type in the kernel, so only existence is
  checked, not type equality.)

This check should only be active in replay-aware mode (when
the replay maps are set), to avoid silently masking errors
during normal loading.

### Loading order

Theories are loaded in dependency order (parents before
children), matching the normal `Theory.load_parents` /
`TheoryReader.load_thydata` order. For each theory:

1. `link_parents` — establish theory graph
2. `incorporate_types` / `incorporate_consts` — skip
   already-existing types/consts
3. `dec_sdata` — reconstruct named theorems via `disk_thm`
   (substituting replayed values when available)
4. `DB.bindl` — register theorems in the database
5. `temp_encoded_update` for each thydata entry — decode
   thydata (substituting replayed values in embedded theorems
   via `disk_thm` with `Anon` keys), fire load callbacks for simpsets,
   TypeBase, grammars, etc.

### Coverage and fallback

The merge tool prunes entries not reachable from the desired
exports. Consequently:

- **Included theories**: all named exports that were live in
  the merge get replayed values (via F lines). Thydata-embedded
  theorems that were live get replayed values (via G lines).
- **Excluded theories**: theories not in the merge's dependency
  closure have no replayed values. All their theorems load as
  DISK_THMs via the normal path. This is safe — the theory
  structure is fully populated, just without verified
  derivations.
- **Partially included theories**: some named exports or
  thydata theorems may have been pruned by the merge (not
  reachable from the desired exports). These fall back to
  DISK_THM creation. The theory structure is complete; only
  the derivation quality differs.

After loading completes, the replay map is cleared (ref set
back to NONE).

## Compression

### Overview

Trace files (`.pft`) are plain text and compress well (~4:1
with zstd or gzip). Compression is applied automatically after
recording and decompressed transparently when reading.

All compression logic is encapsulated in the `TraceCompress`
module, which provides a uniform API for compressing, opening,
and discovering trace files regardless of compression format.

### Tool selection

The `HOL_PFT_COMPRESS` environment variable selects the tool:
- **Unset or empty**: default to `zstd`
- **Set to a tool name**: `zstd`, `gzip`, or `zip`
- **Set to `none`**: disable compression

At activation time, `TraceCompress` verifies the tool exists
on PATH. If not found, falls back to no compression with a
warning.

### Supported tools

| Tool | Compress | Decompress | Extension |
|------|----------|------------|-----------|
| `zstd` | `zstd --rm <path>` | `zstd -dc <path>.zst > tmp` | `.zst` |
| `gzip` | `gzip <path>` | `gzip -dc <path>.gz > tmp` | `.gz` |
| `zip` | `zip -jm <path>.zip <path>` | `unzip -p <path>.zip > tmp` | `.zip` |

All tools replace the original `.pft` file with the compressed
variant. Extensions are appended: `foo.pft` → `foo.pft.zst`.

### TraceCompress module

```sml
signature TraceCompress = sig
  (* Compress a .pft file in-place. Returns the final path
     (with compression extension, or unchanged if disabled). *)
  val compress : string -> string

  (* Open a trace file for reading. Probes for the base path
     and compressed variants (.zst, .gz, .zip). Decompresses
     to a temp file if needed. Returns (instream, cleanup_fn)
     where cleanup_fn removes any temp file. *)
  val open_trace : string -> TextIO.instream * (unit -> unit)

  (* Find a trace file. Given a base path (without compression
     extension), returns SOME of the actual path, or NONE. *)
  val find_trace : string -> string option

  (* Ensure a trace file is decompressed on disk. Returns the
     path to the (possibly decompressed) file. Used by MergeTrace
     for Posix fd-based random access during Pass 1. *)
  val ensure_decompressed : string -> string

  (* File suffixes to search for when scanning directories,
     e.g. ["Theory.pft", "Theory.pft.zst", ...] *)
  val trace_suffixes : string list
end
```

### Where compression happens

- **Recording**: `TraceRecord.export_hook` calls
  `TraceCompress.compress` after writing the final `.pft` file.
  Both theory traces and heap traces are compressed.
- **Merged traces**: NOT compressed (user-facing output,
  typically piped directly to replay).

### Where decompression happens

- **MergeTrace**: uses two access patterns per file.
  Pass 1: `TraceCompress.open_trace` for sequential reading,
  plus `TraceCompress.ensure_decompressed` to obtain a file
  path for Posix fd-based random access (seeking to P entry
  byte offsets during backward reachability).
  Pass 2: `TraceCompress.open_trace` for sequential re-reading.
  Decompressed temp files are cached across both passes
  (decompress once) and cleaned up after.
- **ReplayTrace**: calls `TraceCompress.open_trace`.
- **File discovery**: merge tool uses `TraceCompress.find_trace`
  and `TraceCompress.trace_suffixes` when scanning `-d`
  directories for trace files. `find_heap_trace_file` uses
  `TraceCompress.find_trace`.

### Leftover temp files

**Decompression temp files** (created by `open_trace`):
- Normal cleanup: caller invokes the cleanup function.
- Crash/interrupt: `TraceCompress` maintains an internal list
  of active temp files and registers an `atExit` handler to
  remove them. This covers normal exit and uncaught exceptions
  but not SIGKILL. SIGKILL leftovers are cleaned by
  `Holmake cleanAll` (if under `.hol/`) or OS temp cleanup
  (if using system temp dir).

**Compression failure** (in `compress`):
- `zstd --rm` writes the compressed file, then removes the
  original. If interrupted between these steps, both files
  exist. `find_trace` prefers the uncompressed file if both
  exist. Next build overwrites. No data loss.
- If compression fails entirely, the original `.pft` remains.

### Gitignore

Theory traces are under `.hol/` — already gitignored regardless
of extension. Heap trace gitignore patterns use `*.pft*` globs
to cover all compression extensions:
- `bin/.gitignore`: `hol.state*.pft*`
- `.gitignore`: `src/num/termination/numheap.pft*`
