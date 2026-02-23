# HOL4 Proof Trace Format (`.pftrace`)

Produced by `TraceRecord` + `TraceExport` (stdknl with `HOL_TRACE_PROOFS=1`).
Verified by `ReplayTrace`.

## Overview

A `.pftrace` file records every kernel inference step needed to derive
a theory's exported theorems. Files may be compressed (`.pftrace.zst`
or `.pftrace.gz`). Each file contains type, term, and theorem entries
interleaved in dependency order, followed by a theory name and export
entries.

## Grammar

```
trace     ::= body theory exports
body      ::= entry*
entry     ::= type_entry | term_entry | thm_entry | compute_init
theory    ::= "T " name "\n"
exports   ::= export_entry*

type_entry   ::= "Y " id " V " name "\n"
               | "Y " id " O " thy name argid* "\n"

term_entry   ::= "M " id " V " name tyid "\n"
               | "M " id " C " thy name tyid "\n"
               | "M " id " A " fid xid "\n"
               | "M " id " L " vid bid "\n"

thm_entry    ::= "P " id " " rule args "\n"

compute_init ::= "C " compute_init_args "\n"

export_entry ::= "E " name " " thmid "\n"
```

## Fields

- **name**: unquoted token or quoted string (`"..."` with `\"`, `\\`, `\n`, `\xNN` escapes)
- **id** and similar: non-negative integers
- IDs are scoped to their section: type IDs (Y), term IDs (M),
  theorem IDs (P) are in separate namespaces

## Theorem Rules

Each `P` entry constructs a theorem using a kernel inference rule.
Arguments are rule-specific: a mix of term/type/theorem IDs and
strings. The number and interpretation of arguments is determined
by the rule name. Variable-length arguments always extend to end
of line.

In the table below, `p` denotes a theorem (parent) ID, `t` a term
ID, `y` a type ID, and `str` a (possibly quoted) string.

| Rule | Arguments | Kernel function |
|------|-----------|----------------|
| `REFL` | `t` | `Thm.REFL` |
| `ASSUME` | `t` | `Thm.ASSUME` |
| `BETA_CONV` | `t` | `Thm.BETA_CONV` |
| `ALPHA` | `t t` | `Thm.ALPHA` |
| `ABS` | `p t` | `Thm.ABS` |
| `MK_COMB` | `p p` | `Thm.MK_COMB` |
| `AP_TERM` | `p t` | `Thm.AP_TERM` |
| `AP_THM` | `p t` | `Thm.AP_THM` |
| `SYM` | `p` | `Thm.SYM` |
| `TRANS` | `p p` | `Thm.TRANS` |
| `EQ_MP` | `p p` | `Thm.EQ_MP` |
| `EQ_IMP_RULE1` | `p` | `#1 (Thm.EQ_IMP_RULE)` |
| `EQ_IMP_RULE2` | `p` | `#2 (Thm.EQ_IMP_RULE)` |
| `MP` | `p p` | `Thm.MP` |
| `DISCH` | `p t` | `Thm.DISCH` |
| `INST_TYPE` | `p (y y)*` | `Thm.INST_TYPE` |
| `INST` | `p (t t)*` | `Thm.INST` |
| `SUBST` | `p t (t p)*` | `Thm.SUBST` (original, template, (var, residue) pairs) |
| `SPEC` | `p t` | `Thm.SPEC` |
| `Specialize` | `p t` | `Thm.Specialize` (lazy-beta SPEC) |
| `GEN` | `p t` | `Thm.GEN` |
| `GENL` | `p t*` | `Thm.GENL` |
| `GEN_ABS` | `p t t*` | `Thm.GEN_ABS` (parent, opt_cst (`~` for NONE), vars) |
| `EXISTS` | `p t t` | `Thm.EXISTS` (parent, existential, witness) |
| `CHOOSE` | `p p t` | `Thm.CHOOSE` |
| `CONJ` | `p p` | `Thm.CONJ` |
| `CONJUNCT1` | `p` | `Thm.CONJUNCT1` |
| `CONJUNCT2` | `p` | `Thm.CONJUNCT2` |
| `DISJ1` | `p t` | `Thm.DISJ1` |
| `DISJ2` | `p t` | `Thm.DISJ2` |
| `DISJ_CASES` | `p p p` | `Thm.DISJ_CASES` |
| `NOT_INTRO` | `p` | `Thm.NOT_INTRO` |
| `NOT_ELIM` | `p` | `Thm.NOT_ELIM` |
| `CCONTR` | `p t` | `Thm.CCONTR` |
| `Beta` | `p` | `Thm.Beta` (compute-optimized right-beta) |
| `Mk_comb` | `p p p` | `Thm.Mk_comb` (original, fun result, arg result) |
| `Mk_abs` | `p p` | `Thm.Mk_abs` (original, body result) |
| `DEF_TYOP` | `p t str str` | `Thm.prim_type_definition` (witness, concl, thy, tyop) |
| `DEF_SPEC` | `p t str str*` | `Thm.prim_specification` (witness, concl, thyname, cnames) |
| `COMPUTE` | `t p*` | `Thm.compute` (input term, code equation parents) |

### Compute Initialization

The `C` entry records initialization arguments for `Thm.compute`.
It must appear at most once, before any `COMPUTE` theorems.

```
C y y (str t)* ; (str p)*
```

Arguments: `cval_type`, `num_type`, then cval `(name, term)` pairs
until `;`, then char_eqn `(name, parent)` pairs until end of line.

### Trust Entries

These represent the trust boundary of a trace file.

| Rule | Arguments | Meaning |
|------|-----------|---------|
| `AXIOM` | `t` | Axiom introduction |
| `ORACLE` | `str t t*` | Oracle theorem (tag, concl, hyps) |

`ORACLE` with tag `DISK_THM` has a different format in per-theory traces:
- `ORACLE DISK_THM str str`: ancestor theorem reference (theory, name).
  Replaced by direct theorem references in merged traces.

## Semantics

- **Types and terms** are in topological order: sub-components have
  smaller IDs.
- **Theorems** reference types, terms, and earlier theorems by ID.
- Y, M, P, and C entries are interleaved in dependency order:
  each entry only references IDs that were defined by earlier entries.
- **T** and **E** entries appear at the end of the file after all
  Y/M/P/C entries.
- **Mk_comb**: original eq thm (`A |- t = u v`), fun sub-result
  (`A' |- u = u'`), arg sub-result (`A'' |- v = v'`).
- **Mk_abs**: original eq thm (`A |- t = \x.u`), body sub-result
  (`A' |- u = u'`).
- **SUBST**: original thm, template term, then (variable, residue thm)
  pairs.
- **COMPUTE** theorems use the closure established by the `C` entry.
- **Exports** map theorem names to theorem IDs.

## Merged Traces

The merge tool combines per-theory traces into a single self-contained
trace suitable for from-scratch replay. The merged format is the same
syntax as per-theory traces with the following properties:

- **No `T` line** (or `T merged`)
- **No ORACLE DISK_THM entries** — all ancestor theorem references
  are resolved to direct theorem IDs
- **No unreachable entries** — every type, term, and theorem in the
  file is a dependency of at least one export
- **No duplicates** — types, terms, and theorems are globally
  deduplicated across all source theories
- **Exports** list only the desired theorems

A merged trace can be replayed from scratch in a bare kernel session
with only min theory loaded (`bin/hol --min`).

## Merge Tool

The merge tool combines per-theory traces into a single self-contained
trace for from-scratch replay. Given a set of desired exports
`(theory, name)`, it produces a minimal merged trace.

### Algorithm

**Pass 1 (backward, reverse dependency order): determine what's needed**

For each theory, starting from the theories that contain the desired
exports and working backward through ancestors:

1. Read the theory's trace file
2. Build a parent graph: for each P entry, extract which other P
   entries it references as parents (requires per-rule parsing of
   arguments to distinguish parent IDs from term/type IDs)
3. Walk backward from the needed theorem IDs (initially the desired
   exports; for ancestor theories, the theorems referenced via
   ORACLE DISK_THM by their descendants)
4. Record the set of live P/Y/M/C entry IDs for this theory
5. When the walk hits an ORACLE DISK_THM `(thy, name)`, add that
   to the set of needed ancestor exports

Per-theory memory: parent graph (array of int lists, discarded
after each theory). Cross-theory state: `needed_exports` set.

**Pass 2 (forward, dependency order): write merged trace**

Persistent state across theories:
- Global type dedup map: `type_descriptor → global_type_id`
- Global term dedup map: `term_descriptor → global_term_id`
- Ancestor export map: `(theory, name) → global_theorem_id`
- Global ID counters for types, terms, theorems

Per-theory (discarded after each theory):
- Local-to-global remap arrays for types, terms, theorems

For each theory, read its trace file again. For each live entry:

- **Y entry**: Build a type descriptor from the entry using
  already-remapped global arg IDs. Look up in global type map.
  If found, record local→global mapping (no output). If new,
  assign global ID, write Y line, record mapping.
- **M entry**: Same approach using global type/term IDs. Application
  descriptors are `(A, global_fid, global_xid)` — just two ints.
- **P entry**: If ORACLE DISK_THM, look up `(thy, name)` in ancestor
  export map, record local→global mapping (no output). Otherwise,
  remap all argument IDs to global, assign new global theorem ID,
  write P line.
- **C entry**: Remap and write.

After all live entries: register this theory's live exports in
the ancestor export map.

After all theories: write E lines for the desired exports.

### Type/term dedup descriptors

Type descriptors:
- Type variable: `(V, name)`
- Type operator: `(O, thy, name, [global_arg_ids])`

Term descriptors:
- Variable: `(V, name, global_tyid)`
- Constant: `(C, thy, name, global_tyid)`
- Application: `(A, global_fid, global_xid)`
- Lambda: `(L, global_vid, global_bid)`

These are lightweight tuples of strings and ints, compared
structurally. For applications (the most common kind), the
descriptor is just two ints.

### Theorem dedup

Currently no theorem dedup is performed — each non-DISK_THM P entry
gets a fresh global ID. This is a potential future optimization.
Two possible approaches:

1. **Derivation-based**: Two P entries with the same rule and
   identical remapped arguments (after type/term/theorem dedup)
   produce the same theorem. Low overhead — the remapped entry
   is already computed. But incomplete: different derivations of
   the same theorem are not deduplicated.

2. **Statement-based**: Record the theorem statement (conclusion +
   hypothesis term IDs) in each P entry. Full dedup but increases
   trace size. Requires a format addition (e.g., `= concl hyps...`
   suffix on P lines).

Empirical data from large merges will determine whether theorem
dedup is worthwhile and which approach to use.

### Complexity

- Each per-theory file read twice (backward pass + forward pass)
- Per-theory work is linear in the number of entries
- Global type/term maps: O(log N) per lookup (red-black map)
- Memory: global type map (small, thousands of entries) +
  global term map (dominant cost, ~40 bytes per unique term) +
  per-theory remap arrays (discarded after each theory)

For HOL's 180 theories (~12.5M total term entries): estimated
~240MB for the global term dedup map.

## Compression

Files may be stored as `.pftrace.zst` (preferred) or `.pftrace.gz`.
The replayer auto-detects format from extension.

## Recording and Export

Per-theory traces are produced during `HOL_TRACE_PROOFS=1` builds
by `TraceRecord` (recording) and the export hook.

### Recording

`TraceRecord` sets `Thm.trace_hook` to intercept every kernel
inference rule. On each call it:

1. Interns any new types/terms referenced by the rule, writing
   `Y`/`M` entries to the output stream immediately
2. Resolves parent theorem references to their theorem IDs via
   `id_to_line` (a map from kernel `trace_id` to file theorem ID).
   If a parent is not in the map (a heap theorem from before tracing
   started), an `ORACLE DISK_THM` entry is emitted on demand.
3. Writes the `P` entry (or `C` for COMPUTE_INIT) to the output

The output stream is opened on the first write, piped through a
compressor (zstd preferred, gzip fallback, uncompressed if neither
available) to a temporary file in the build directory.

### In-memory state

- **`ty_map`**, **`tm_map`**: structural dedup maps for types/terms.
  Each unique type/term gets one ID; the Y/M entry is written on
  first encounter.
- **`id_to_line`**: maps kernel `Thm.trace_id` to file theorem ID.
  Updated on each P entry. Used to resolve parent references.
- **`lines_written`**: next theorem ID to assign (counter for P entries).
- **`compute_init_data`**: saved `Thm.compute` init args, for re-emitting
  the C entry in each theory that uses COMPUTE.

### Export

`TraceRecord` sets `Thm.trace_export_hook` which fires at
`export_theory()` time with the theory name and named exports.
It:

1. Writes `T <thyname>`
2. Writes `E <name> <thm_id>` for each exported theorem (looking
   up the theorem ID via `id_to_line`)
3. Closes the compressor pipe
4. Renames the temporary file to `<thyname>Theory.pftrace.zst`
   (or `.gz` or `.pftrace`)
5. Resets all in-memory state for the next theory
