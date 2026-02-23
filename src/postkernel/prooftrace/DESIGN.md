# HOL4 Proof Trace System

## Overview

The proof trace system records kernel inference steps during HOL4
builds and produces self-contained trace files that can be replayed
from scratch for independent verification.

The pipeline has three stages:
1. **Recording**: per-theory `.pftrace` files produced during
   `HOL_TRACE_PROOFS=1` builds
2. **Merging**: per-theory traces combined into a single
   self-contained trace for the desired exports
3. **Replay**: merged trace replayed from scratch in a bare kernel
   session (`bin/hol --min`) to verify exports are oracle-free

## Trace Format (`.pftrace`)

### Grammar

```
trace        ::= entry* name exports
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
- N and E entries appear at the end

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
| `DEF_TYOP` | `p t s s` — witness, concl, thy, tyop |
| `DEF_SPEC` | `p t s s*` — witness, concl, thyname, cnames |
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

In-memory state:
- `ty_map`, `tm_map`: structural dedup maps (type/term → ID)
- `id_to_line`: kernel trace_id → file theorem ID
- `lines_written`: next theorem ID counter

At `export_theory()` time, the export hook appends N and E entries,
closes the compressor, renames the temp file to
`<thyname>Theory.pftrace.zst`, and resets state.

Per-theory traces include all steps recorded during the process,
including library loading. No filtering is done — the merge tool
handles that.

## Merge Tool

Input: list of per-theory `.pftrace` file paths, plus desired
exports `(theory, name)`.

Output: single self-contained `.pftrace` with only entries
reachable from the desired exports, types/terms globally
deduplicated, DISK_THM resolved.

### Pass 1: Determine what's needed

Starting from the desired exports, work backward to discover all
needed entries and ancestor theories:

1. Load the trace for each theory containing a desired export
2. Build a parent graph (per-rule parsing to extract theorem
   parent IDs from P entry arguments)
3. Walk backward from the needed theorem IDs, marking live entries
4. When the walk hits a DISK_THM entry (thy, name), record that
   as a needed ancestor export. If the ancestor's trace hasn't
   been processed yet, load it and repeat from step 2.

This processes each theory at most once, discovering ancestor
dependencies as it goes. Only traces that are transitively
needed are loaded.

After this pass, we have a set of live entry IDs per theory and
a topological ordering of the needed theories.

### Pass 2: Write merged trace

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

Process theories in dependency order. For each theory's live entries:
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
min theory loaded). Types and terms are constructed lazily on demand
to ensure definitions are replayed before the types/terms they
define are referenced. Each P entry is replayed through the actual
kernel inference rule. Exports are checked to be oracle-free.

## Compression

Files may be `.pftrace.zst` (preferred), `.pftrace.gz`, or
uncompressed `.pftrace`. Auto-detected from extension.
