# PFTEmit / PFTMerge review notes

Context: broad replay appears to work, but merge can OOM and there are architectural/performance questions. These notes summarize correctness risks, performance issues, and possible design improvements.

## Executive summary

1. **PFTMerge still has a major ID-reuse design issue.** It allocates all new IDs for all included commands before emission. DEL/freeing happens only during emission, after all allocations have already occurred, so the free-list allocator does not actually reduce the footer limits. The merged trace's ID-space is closer to total reachable objects than peak live objects.

2. **PFTMerge still stores very heavy per-command metadata.** Lazy file ingestion helps, but once a file is loaded, every command gets a boxed record with list-allocated dependency pairs. Large Candle files can still OOM.

3. **Candle PFTEmit is now parallel-friendly in principle.** The former module-global compute-preamble state has been removed, and `PFTCandleComputePreamble.emit_file` emits the standalone Candle compute preamble / `COMPUTE_INIT`.

4. **HOL4 compute initialization is still inline.** HOL4 per-theory emission should not yet be considered fully parallel-clean if multiple theory files contain compute uses.

---

## PFTMerge review

### 1. Major issue: ID reuse does not actually happen

`PFTMerge` has an `IdAlloc` with `release`, and during emission it does:

```sml
if rc = 0 then (PFTWriter.del out ...; free_id ns nid)
```

But all IDs are allocated earlier in Step 1:

```sml
(* Step 1: Allocate new IDs for all included commands *)
...
set_rename fi ns id (alloc_id ns)
```

This happens for every included command before any emission and before any `free_id` calls.

Therefore:

- `free_id` during emission cannot affect any future allocation, because all allocations are already done.
- The free list is essentially useless.
- Output IDs are not reused.
- Footer limits are not tight peak-live limits; they are closer to total reachable allocations.

This is likely a major performance problem for replay and merged trace memory limits.

#### Better design

Allocate IDs online during emission.

During pass2 emission, scan commands in topological order:

1. For each included command, consumed IDs already have renames because producers appear earlier.
2. Allocate new IDs for the command's produced objects now.
3. Emit the command.
4. Decrement consumed object refcounts.
5. When an old-object refcount hits zero, emit DEL and release that object's new ID.

This makes `IdAlloc.release` useful and should greatly reduce footer limits.

#### Required refactor

Current refcounts are keyed by **new IDs**. For online allocation, it is more natural to count references by **old object identity**:

```text
(file_idx, namespace, old_id) -> remaining uses
```

Then during emission:

- old object has a current new ID in the rename table,
- decrement old-object refcount after each use,
- when zero, DEL/free the associated new ID.

This is a larger refactor, but high leverage.

---

### 2. Per-command metadata is too heavy

Even with lazy file ingestion, once a file is loaded, the whole file is represented as:

```sml
type cmd_meta = {
  produced : (int * int) list,
  consumed : (int * int) list,
  kind : cmd_kind,
  opcode : int,
  ref_name : string option
}
```

For large Candle traces this is very expensive:

- record per command,
- list cells per dependency,
- boxed `(ns,id)` pairs,
- datatype values,
- option values.

For millions of theorem commands, this can dominate memory.

#### Better representation

Use compact parallel arrays and flat dependency arrays:

```sml
cmd_kind     : int DArray
opcode       : int DArray
prod_start   : int DArray
prod_len     : int DArray
cons_start   : int DArray
cons_len     : int DArray
ref_name_idx : int DArray

prod_ns      : int DArray
prod_id      : int DArray
cons_ns      : int DArray
cons_id      : int DArray
```

For command `ci`, dependencies are stored in slices of the flat arrays:

```text
cons_start[ci] ... cons_start[ci] + cons_len[ci] - 1
```

This preserves the current graph algorithm but should greatly reduce memory.

Lazy loading reduces the number of loaded files. Compact metadata reduces the cost of each loaded file. If a target depends on one huge file, lazy loading alone is not enough.

---

### 3. Lazy loading is useful but file-granularity may be too coarse

The current lazy-loading design loads full metadata for a file as soon as any command in that file is needed.

If a target depends on one theorem in a huge dependency file, PFTMerge still loads the entire file's metadata.

#### More ambitious alternative

Build a lighter per-file index:

- command byte offsets,
- producer table,
- save/name introducers.

Then during reachability, seek/read only needed commands.

However, the current `PFTReader` API is streaming and does not expose command offsets or seeking. This would require extending `PFTReader` or writing a lower-level indexed reader.

Probably not the first thing to do. First try compact metadata and online allocation.

---

### 4. Name-introducer model assumes one introducer per name

PFTMerge follows name-level dependencies:

```sml
CONST/TYOP ref_name -> const_introducer/type_introducer
```

This assumes a global unique introducer for each name.

This is okay if:

- inputs are topologically sorted,
- each logical constant/type is introduced once,
- duplicate input files are avoided.

Duplicate theory files can cause duplicated ingestion and save-table overwrites. This was noticed in `emit-candle-merged.sml` and should be avoided.

---

### 5. Refcount computation still requires included metadata

For DEL insertion, PFTMerge computes refcounts before emission. This is natural, but memory-heavy.

If redesigned around old-object refcounts and online allocation, it still needs a pre-emission count pass over included commands, but the counts can be stored compactly in arrays parallel to old IDs:

```sml
old_refcount[fi][ns][old_id] : int
```

Only for loaded files.

This pairs well with online ID allocation.

---

## PFTEmit review

### 1. Candle parallelism obstacle fixed

The previous module-global Candle compute-preamble state has been removed. Candle `PFTEmit` no longer emits the compute preamble or
`COMPUTE_INIT` inline. Instead, `PFTCandleComputePreamble.emit_file` emits a
standalone compute-preamble PFT, including the single stateful `COMPUTE_INIT`.

Candle per-theory PFTs now only LOAD compute-preamble helper theorems by name
and emit `COMPUTE` commands. This makes Candle `emit_theory` essentially
independent per theory and suitable for parallel per-theory generation.

Important caveat: merge/replay order still matters. The standalone compute
preamble must be placed after its prerequisites (`bool`, `num`, `arithmetic`,
`prim_rec`, `cv`) and before any reachable `COMPUTE` use. HOL4 output still
emits `COMPUTE_INIT` inline from trace `compute_args`; HOL4 parallelization is
a separate future design problem.

---

### 2. PFTEmit per-theory emission status

For Candle, per-theory emission is now mostly parallelizable:

- each `emit_theory` parses one trace,
- writes one PFT,
- has local ID counters/memos,
- emits Disk dependencies as LOADs by name,
- handles within-theory definitions locally by `check_def`,
- assumes the static and compute preambles are supplied separately in merge/replay order.

For HOL4, compute initialization is still emitted inline and should not yet be
considered fully parallel-clean if multiple theory files contain compute uses.

---

### 3. PFTEmit emits monotonic IDs intentionally

`PFTEmit.sig` says per-theory PFTs allocate IDs monotonically and use DEL only as hints.

That is okay. PFTMerge is supposed to compact/reuse IDs. The more serious issue is that PFTMerge currently does not actually reuse IDs effectively.

---

### 4. PFTEmit performance hot spots

Candle derivations are verbose. Most output blowup likely comes from derived Candle reconstruction:

- `do_MP`,
- `do_DISCH`,
- `do_GEN`,
- `do_SPEC`,
- `do_EXISTS`,
- `Def_spec_prf`,
- `Def_tyop_prf`,
- `SUBST_prf`.

High-leverage improvements include:

- stronger Candle preamble lemmas,
- theorem-command memoization (`c_refl`, `c_beta`, `c_inst`, `c_inst_type`, `do_beta_reduce`),
- SUBST subtree skipping when occurrence analysis proves no substitution redex occurs below a subtree.

---

### 5. PFTEmit correctness risks still worth noting

Known class of risk: derived translations using `ABS_THM` under hypotheses.

Fixed:

- `SUBST_prf` freshens under binders and bridges back to the original result names.

Possible future sites if replay failures appear:

```sml
Def_spec_prf:
  else c_abs f (cong x)
```

```sml
GEN_ABS_prf:
  c_abs v_tm th_acc
```

Since replay is currently good, these can be deferred until there is concrete evidence.

---

## Design for parallel individual PFTs

Clean pipeline design:

### Stage 1: Generate static preambles

```text
candle-preamble.pft.bin
candle-compute-preamble.pft.bin
```

### Stage 2: Emit per-theory PFTs in parallel

Each theory PFT:

- assumes preambles are available by SAVE names,
- LOADs cross-theory theorem dependencies,
- does not emit global preamble material.

This makes `PFTEmit.emit_theory` essentially independent per theory.

### Stage 3: Merge

Input order should be:

1. Candle base preamble,
2. per-theory files up to and including the compute preamble prerequisites,
3. Candle compute preamble if needed,
4. remaining per-theory files in dependency/topological order.

Merge still needs topological order because LOAD requires prior SAVE in the logical stream, but **emitting** per-theory files can be parallel.

---

## Highest-leverage future work

For PFTMerge OOM/performance:

1. **Online ID allocation / real ID reuse in merge**
   - high impact for merged footer limits and replay memory,
   - aligns implementation with PFTMerge's intended DEL/compaction role.

2. **Compact `cmd_meta` representation**
   - high impact for merger memory/OOM.

3. **Old-object refcount arrays**
   - likely needed for online allocation.

4. **Optional indexed/on-demand command loading**
   - more ambitious, only if compact metadata still OOMs.

For parallel PFT generation:

1. Update drivers/scripts to actually launch independent Candle `emit_theory` jobs in parallel.
2. Keep merge input order explicit: base preamble, prerequisite theories, compute preamble, remaining theories.
3. If HOL4 parallel output matters, design an external HOL4 compute-init story; currently only Candle has been cleaned up.
