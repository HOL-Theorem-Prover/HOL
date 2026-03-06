# HOL4 Proof Trace Design

## Overview

Record kernel inference steps during HOL4 builds, producing trace
files that can be merged and replayed from scratch for independent
verification (no DISK_THM oracles).

Pipeline: **Record → Export → Merge → Replay**

## Kernel Changes

The `thm` datatype gains an `int` trace ID from a monotonic
per-process counter, saved and restored with heaps:

```sml
datatype thm = THM of Tag.tag * term HOLset.set * term * int
val trace_counter : int ref
```

Two hook refs, both `NONE` by default:

```sml
val trace_hook : (trace_step -> unit) option ref
val trace_export_hook :
  (string -> thm_export list -> unit) option ref
```

`trace_hook` is called after each inference rule. Its return value
is discarded and exceptions are caught. `trace_export_hook` is
called at `export_theory` time with the theory name and all
theorem exports — both named (`save_thm` etc.) and anonymous
(theorems stored in theory data by TypeBase, simpsets, decision
procedures, etc., discoverable via TheoryDelta). The export list
includes trace IDs for all theorems that later theories may
reference.

When both hooks are `NONE`: overhead is 8 bytes per thm + one ref
deref per inference rule.

### Specialize_thm

`Specialize(t, th)` requires the term `t` as an argument, which
must be interned. On the EVAL hot path, rewrite rules are
specialized frequently with terms that may be large and
cache-cold.

`Specialize_thm(witness_thm, th)` is a kernel rule variant that
takes a theorem whose conclusion provides the specialization
term, needing only two trace IDs and no term interning. This is
a 2-line kernel addition (matching PR #1825 commit `641a2703d`)
that keeps the EVAL hot path free of term interning.

## Trace Step Types

```sml
datatype trace_step =
  (* No term arguments — O(1) recording *)
    TR_SYM | TR_TRANS | TR_MK_COMB | TR_MP | TR_EQ_MP
  | TR_CONJ | TR_CONJUNCT1 | TR_CONJUNCT2
  | TR_NOT_INTRO | TR_NOT_ELIM
  | TR_EQ_IMP_RULE1 | TR_EQ_IMP_RULE2
  | TR_DISJ_CASES | TR_Beta
  (* Parent-derived terms — O(1) recording *)
  | TR_REFL_RATOR | TR_REFL_RAND | TR_REFL_BODY
  | TR_Mk_comb_v | TR_Mk_abs_v
  | TR_Specialize_thm
  (* Term arguments required *)
  | TR_ASSUME | TR_REFL | TR_BETA_CONV | TR_ALPHA
  | TR_ABS | TR_GEN_ABS | TR_INST_TYPE | TR_DISCH
  | TR_SPEC | TR_Specialize | TR_GEN | TR_GENL
  | TR_EXISTS | TR_CHOOSE | TR_DISJ1 | TR_DISJ2
  | TR_CCONTR | TR_INST | TR_SUBST
  | TR_AP_TERM | TR_AP_THM
  | TR_ORACLE | TR_AXIOM | TR_DEF_TYOP | TR_DEF_SPEC
  | TR_COMPUTE | TR_DISK
```

Each constructor carries the result thm, parent thms, and any
term/type arguments needed for replay. `TR_DISK` is the ML-side
representation of theorems loaded from disk; it maps to NAME or
LOAD entries in the trace format (not a distinct format rule).

## Recording

Activated by a `--trace` flag to `Holmake` (and `bin/build`),
which sets the `HOL_TRACE_PROOFS` environment variable for child
processes. Each process checks this on startup, setting
`trace_hook` and `trace_export_hook`.

### Stale stream handling

When a process loads a saved heap, the recording module's output
stream is stale (from the heap build's session). The new process
is detected by comparing the current PID against a saved
`session_pid` ref — after heap restore, the PID differs. On
mismatch, the stale stream is closed and a new output is opened.
Intern tables and caches are reset for the new session.

### In-memory state

- **Term stack** (depth 16): recent term ML values
- **Theorem stack** (depth 16): recent trace IDs
- **Term hash cache** (64K entries, direct-mapped):
  `Term.hash` mod 64K → (term, term\_id), checked by pointer-eq
- **Type map**: `Redblackmap` keyed by `Type.compare`
  (types are small and few; no hash cache needed)
- Sequential ID counters for types and terms

No unbounded structures. The term cache is fixed-size; the type
map grows modestly (thousands of entries, not millions).

If the cache hit rate proves insufficient (terms evicted and
re-serialized too often), a backup `Redblackmap` with hash-first
comparison (as in PR #1825) can be added behind the cache for
earlier dedup. This is a self-contained change to the recording
module.

### Per-step recording

All output goes to a single temp file, entries interleaved in
dependency order (Y for types, T for terms, P for proof steps).

**Theorem-only rules** (TRANS, MK_COMB, SYM, MP, etc.):
Write P entry with rule tag and parent trace IDs. Parent refs
check the theorem stack first — `^k` if hit, explicit ID if
miss. O(1).

**REFL_RATOR / REFL_RAND / REFL_BODY** (Mk_comb and Mk_abs
internal REFLs): Write P entry with rule tag and parent trace
ID. No term data. O(1). The replayer reconstructs the term
from the parent theorem's conclusion.

**Specialize_thm**: Write P entry with two parent trace IDs
(witness theorem + universally quantified theorem). No term
data. O(1). The replayer extracts the specialization term from
the witness theorem's conclusion.

**Rules needing terms** (SPEC, DISCH, ABS, REFL, ASSUME, etc.):
Intern each term argument:
1. Check term stack by pointer-eq → `~k` reference. O(1).
2. Check hash cache by `Term.hash` + pointer-eq → term ID. O(1).
3. Miss → recursively serialize: sub-terms go through the same
   lookup; types go through the type map. Write Y/T entries,
   assign new IDs, update cache and stack. O(term\_size).

Write P entry referencing the term by stack ref (`~k`) or ID.
When a term was just interned (cache miss), it is now on top
of the stack, so `~0` can be used.

### Compute init

The `I` entry records initialization arguments for `Thm.compute`
(cval type, num type, 29 cval name/term pairs, char equation
parents). At most one per trace, emitted before any COMPUTE P
entry. This avoids repeating the large fixed set of compute
primitives in every COMPUTE step.

### Constant and type declarations

A `Theory.register_hook` callback fires on `NewConstant` and
`NewTypeOp` TheoryDelta events. Constants/types introduced by
definitions (DEF_SPEC, DEF_TYOP) already have P entries.
Declarations without definitions are recorded as C/O entries.

## Export

At `export_theory` time, the export hook receives all theorem
exports — named and anonymous — with their trace IDs.

1. Closes the temp file.
2. **Pass 1 (backward):** Scan P entries from the end. Maintain
   a bitset of needed trace IDs (seeded with the exported
   theorem trace IDs). For each needed P entry, mark its
   parent trace IDs as needed. Also collect the Y/T IDs
   referenced by needed P entries. If any COMPUTE P entry is
   needed, the I entry and all its Y/T/P dependencies are
   also marked needed. C/O entries' type references (Y IDs)
   are included in the needed Y set.
   The backward scan uses the fixed-width line-length suffix
   (see Trace Format): read the last 8 bytes to get line
   length, seek back, parse, repeat. O(1) per line.
3. **Expand Y/T set:** Forward scan of Y/T entries. For each
   needed T entry, mark its sub-term T and sub-type Y
   references as needed. (Dependencies point to lower IDs,
   so one forward pass suffices.)
4. **Pass 2 (forward):** Read the temp file. Write only needed
   Y/T/P entries to the final `.pft` file, remapping IDs to
   be sequential. Append C/O declarations, N (theory name),
   and E (export name/id → trace ID) lines.
5. Compress the `.pft` file (zstd or gzip, modular — similar
   to PR #1825's TraceCompress).
6. Delete the temp file.

**Heap traces** do not have an `export_theory` call, so no
export-time filtering is performed. Heap traces are written
directly to their final location and contain all recorded
steps. The merge tool handles liveness filtering for heap
traces.

## Trace Format (.pft / .pft.zst)

Text format, one entry per line. Each line ends with a
fixed-width length suffix `@NNNNNN\n` (6-digit zero-padded
byte count of the full line including the suffix and newline).
This enables efficient backward scanning for export-time
filtering without sacrificing human readability.

Compressed with zstd by default; compression module is
pluggable.

```
V <version>
H <heap_path>                          (if built on a heap)
Y <id> V <name>                        (type variable)
Y <id> O <thy> <name> <arg_ids...>     (type operator)
T <id> V <name> <type_id>              (term variable)
T <id> C <thy> <name> <type_id>        (term constant)
T <id> A <func_id> <arg_id>            (application)
T <id> L <var_id> <body_id>            (lambda)
C <thy> <name> <type_id>               (const declaration)
O <thy> <name> <arity>                 (type declaration)
I <cval_type_id> <num_type_id> ...     (compute init, at most once)
P <trace_id> <rule> <args...>          (proof step)
N <theory_name>
E <name> <trace_id>                    (named export)
E <trace_id>                           (anonymous export)
```

P entry arguments are trace IDs (for parent theorems, possibly
as `^k` stack refs) and term/type IDs (possibly as `~k` stack
refs). Rules that derive terms from parents (REFL_RATOR, etc.)
take only parent trace IDs.

Cross-file references for ancestor theorems from other theories
(needed because parallel sibling theories have overlapping trace
ID ranges):

```
P <id> NAME <thy> <name>       (named ancestor theorem)
P <id> LOAD <thy> <trace_id>   (anonymous ancestor theorem)
```

Ancestor theorems from heaps are referenced by raw trace ID
(unambiguous because heaps are built sequentially, each
extending the previous counter).

## Merge

Input: per-theory `.pft` files + heap `.pft` files + desired
exports.

Output: single self-contained `.pft` with all cross-file
references resolved, containing only entries reachable from the
desired exports.

1. Load metadata from each file (exports, NAME/LOAD refs,
   heap parent).
2. Topological sort of files by dependency.
3. For each file in order: determine live entries (backward
   reachability from needed exports/references), write live
   entries with globally remapped IDs, resolve NAME/LOAD
   to global IDs.

Cross-file term/type deduplication: as each file's Y/T entries
are processed, a global map from term/type structure to merged
ID avoids emitting duplicates. This is a natural extension of
the ID remapping already needed during merge.

## Replay

Forward pass through merged trace in `hol --min` (kernel only,
no boolTheory).

- Y entries → construct types
- T entries → construct terms
- C/O entries → declare constants/types in the kernel
- I entry → initialize compute primitives
- P entries → call the corresponding kernel inference rule
- E entries → verify the theorem exists and is oracle-free

Types and terms can be constructed lazily (store descriptions,
build on first reference by a P entry) to handle forward
references to constants/types not yet defined.

---

## Deferred Features

### Compound rules (SPECL / SPECIALIZEL)

Consecutive SPEC (or Specialize) entries where each uses the
previous result as its parent can be collapsed into single
SPECL / SPECIALIZEL entries via peephole optimisation. This
reduces trace size and replay overhead. Deferred as a
self-contained optimisation to the recording module.

### Provenance lines and replay-aware theory loading

The merge tool can emit **provenance lines** (F and G) in the
merged trace, mapping global merged IDs back to their
theory-level identifiers:
- `F thy name global_id` — for named theory exports
- `G thy src_trace_id global_id` — for resolved LOAD references

These are consumed by **replay-aware theory loading**, which
substitutes replayed (oracle-free) theorem values during theory
loading, avoiding DISK_THM oracles in interactive sessions after
replay. This requires changes to `disk_thm`, `SharingTables`,
`incorporate_types`/`incorporate_consts` skip logic, and
`ThyDataSexp`. Deferred as a separate PR orthogonal to the core
record/replay pipeline.

### Replay memory management

For large merged traces, the replayer keeps all constructed
types, terms, and theorems alive for the full forward pass.
Two strategies for reducing peak memory:
- **Last-reference pass**: scan the trace to compute each
  entry's last reference point; null out entries after their
  last use during replay.
- **Merge-side reordering**: reorder entries to minimize the
  maximum live set.

Deferred pending empirical data on replay memory usage.

### Metadata files (.pftm)

For very large trace files, scanning the full `.pft` for
metadata (exports, NAME/LOAD refs, ID ranges) during merge
may be slow. Lightweight `.pftm` metadata files (as in PR
#1825) can cache this information. Deferred pending empirical
data on merge performance.

---

## Design Rationale

### Why streaming, not proof-in-thm?

Storing proof trees inside `thm` (like otknl) causes memory
blowup on large developments. Experiment: proof-in-thm stdknl
used 4.3 GB peak RSS for the HOL build (vs 1.5 GB vanilla) and
OOMed at 12 GB during CakeML's compiler backend proofs. Proofs
reachable from caches, simpsets, and databases cannot be GC'd.
Streaming avoids this entirely — proofs go to disk immediately.

### Why stack + hash cache for terms?

A Redblackmap keyed by `Term.compare` is O(term\_size) per
lookup. On the EVAL hot path with deep terms and billions of
steps, this is prohibitive. PR #1825 went through multiple
iterations to address this.

The stack + hash cache gives O(1) for the common cases (recent
terms via stack, repeated terms via cache) with bounded memory.
Cache misses fall through to full serialization, which is
unavoidable for genuinely new terms. No complex map structures,
no unbounded memory growth. A backup map behind the cache can
be added later if empirical data shows excessive cache misses.

### Why a simple map for types?

Unlike terms, types are small (rarely more than a few nodes)
and there are far fewer unique types in a build. A
`Redblackmap` keyed by `Type.compare` is adequate and simpler
than maintaining a separate hash cache.

### Why REFL_RATOR / REFL_RAND / REFL_BODY?

Mk_comb and Mk_abs internally produce REFL theorems whose
terms are sub-terms of the parent theorem's conclusion. On the
EVAL hot path (billions of Mk_comb steps), serializing these
terms would dominate recording cost. Since the terms are always
derivable from the parent at replay time, recording just the
parent trace ID makes the entire EVAL hot path O(1) per step.

### Why Specialize_thm?

Same principle as REFL_RATOR: avoid term interning on the hot
path by deriving the term from a parent theorem. During EVAL,
rewrite rules are specialized frequently with potentially large
terms. `Specialize_thm` eliminates this cost for the common
case where the specialization term is available as a theorem's
conclusion.

### Why export-time filtering?

A significant fraction of inference steps are not reachable
from exported theorems (the exact ratio is unknown and likely
varies widely across theories). Recording everything to a temp
file and filtering at export time means the final `.pft` trace
contains only what's needed for replay. This reduces the work
for downstream tools (merge, replay) and produces smaller trace
files. The cost is two passes over the temp file at export
time, which is modest compared to the build itself.

### Why compute init (I entry)?

`Thm.compute` depends on a large fixed set of primitives (29
cval name/term pairs, char equation theorems). Recording these
inline in every COMPUTE P entry would be redundant and verbose.
The I entry records them once; COMPUTE entries reference the
initialized state.

### Why compression?

Final trace files can be large (hundreds of MB per theory for
heavy developments). Zstd compression typically achieves 5-10x
reduction on these text traces with minimal CPU overhead. The
compression module is separate from the recording/export logic.

### Why text format?

Human-readable traces are valuable for debugging, inspection,
and trust. The format is simple enough that an independent
verifier can be written from the spec.

### Why cross-file term dedup in merge?

Without dedup, terms shared across theories (common types,
boolean connectives, etc.) would be duplicated in every file
that uses them, inflating the merged trace and slowing replay.
The dedup map's memory cost depends on the number of unique
terms surviving export-time filtering, which is unknown until
we have empirical data. The merge tool runs as a separate
post-build process, so memory pressure during recording is
unaffected. If the dedup map proves too large for very large
developments, the merge could process files in chunks or
fall back to no dedup.
