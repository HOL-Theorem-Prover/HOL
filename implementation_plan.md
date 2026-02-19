# Implementation plan: merged traces for from-scratch replay

## Overview

Refocus the proof trace system around a single use case: producing a
self-contained merged trace file that can be replayed from scratch in a
bare kernel session (or independent checker). Per-theory traces become
build intermediates consumed by a merge tool.

## Phase 1: Simplify per-theory traces

### 1a. Thread theorem name through disk_thm

**Goal:** ORACLE DISK_THM entries record `(theory, name)` instead of
the full theorem statement, avoiding term interning for ancestor theorems.

- `src/prekernel/FinalThm-sig.sml`: add name parameter to `disk_thm`
- `src/thm/std-thm.ML`: pass name to `TR_DISK_THM`
- `src/thm/otknl-thm.ML`: same change for signature compatibility
- `src/thm/trace_step_dtype.sml`: change `TR_DISK_THM` to carry
  `string * string` (theory, name) instead of just `string`
- `src/postkernel/SharingTables.sml`: pass the theorem name to
  `disk_thm` (already available at call site)
- `src/postkernel/ThyDataSexp.sml`: look up the name from
  `DEP_SAVED` depid and pass it to `disk_thm`
- `src/postkernel/prooftrace/TraceRecord.sml`: write
  `ORACLE DISK_THM <thy> <name>` (no statement interning)
- `src/postkernel/prooftrace/TraceExport.sml`: remove
  `ext_thm_cache` and all statement-caching machinery

### 1b. Remove PARENTS and ANCESTOR from header

- `src/postkernel/prooftrace/TraceExport.sml`: remove PARENTS line,
  ANCESTOR lines, sha256sum computation
- `src/postkernel/prooftrace/FORMAT.md`: update grammar and header

### 1c. Fix COMPUTE recording and replay

**Goal:** Record all arguments to `Thm.compute` so replay calls the
same kernel entry point. No result term in the trace.

Add `TR_COMPUTE_INIT` to trace_step (fires once when `Thm.compute`
is called with init args):

```sml
| TR_COMPUTE_INIT of (string * term) list  (* cval_terms *)
                   * hol_type               (* cval_type *)
                   * hol_type               (* num_type *)
                   * (string * 'a) list     (* char_eqns *)
```

This does not produce a theorem. It is an error for it to occur more
than once, and an error for TR_COMPUTE to occur before it.

Change `TR_COMPUTE` to carry only the code equation thms and input
term (result is computed by replay, not recorded):

```sml
| TR_COMPUTE of 'a * 'a list * term
              (* result, code_eqn_thms, input_term *)
```

Changes:
- `src/thm/trace_step_dtype.sml`: update both constructors
- `src/thm/std-thm.ML`: fire `TR_COMPUTE_INIT` at the outer
  `compute` call, simplify `TR_COMPUTE` to drop result eqn
- `src/postkernel/prooftrace/TraceRecord.sml`: write
  `COMPUTE_INIT` line (once) and simplified `COMPUTE` lines
- `src/postkernel/prooftrace/ReplayTrace.sml`: parse
  `COMPUTE_INIT`, build `Thm.compute` closure, use it for all
  COMPUTE steps. Remove `compute_verifier` hook and COMPUTE
  from `opaque_rules`.
- `src/postkernel/prooftrace/FORMAT.md`: document COMPUTE_INIT
  and updated COMPUTE format

### 1d. Remove ext_thm_cache from TraceRecord

Depends on 1a (DISK_THM no longer needs statement caching).

- `src/postkernel/prooftrace/TraceRecord.sml`: remove
  `ext_thm_cache`, `cache_ext_parents`, `cache_ext_thm`,
  `cache_ext_thm_with_thy`, and caching logic in `record_step`
  and `export_hook`

## Phase 2: Build merge tool

### 2a. Merge tool core

New file: `src/postkernel/prooftrace/MergeTrace.sml`

Input: desired theorem names (as `theory.name`), directory of
per-theory traces.

Algorithm:
1. Discover per-theory traces and infer dependency order
2. Read traces in dependency order
3. Maintain global intern tables for types/terms, remap each
   theory's local IDs into the global namespace
4. Maintain global step counter, remap step IDs
5. Replace `ORACLE DISK_THM <thy> <name>` entries with direct
   step ID references, resolved by `(thy, name)` against the
   ancestor export map built incrementally
6. After all theories processed, do reachability analysis from
   the desired export steps to determine live steps
7. Write a single merged `.pftrace` file containing only the
   live steps, with only the desired theorems as exports

### 2b. Memory considerations

The global intern tables for types/terms may be large for full
HOL builds. Benchmark and address if needed (e.g., streaming
approach, or intern per-theory with cross-references).

## Phase 3: Simplify replayer

### 3a. Remove chain verification

Remove from `ReplayTrace.sml`:
- `verify_chain` and all support (`toposort`, `get_parents`,
  `check_ancestors`, `digest_map`, `file_digest`)
- `ancestor_ctx` type, `ctx_lookup`, `ctx_add_exports`
- `replay_file_ctx`
- `compute_verifier` hook (replaced by proper COMPUTE replay)

### 3b. Remove definition workarounds

Remove from `ReplayTrace.sml`:
- `already_defined` checks in DEF_TYOP and DEF_SPEC
- Fallback paths using `mk_defn_thm`
- Just call `prim_type_definition` / `prim_specification` /
  `gen_prim_specification` directly (always succeeds from scratch)

### 3c. Update scripts

- Update `verify_all_traces.sml` to use merge + replay workflow
- Update `bench_traces.sml` similarly
- Update or remove `bench_build.sh` as needed

## Phase 4: Cleanup

- Update FORMAT.md to reflect final format
- Update PR description
- Build timing comparison: current develop vs proposed kernel with
  hooks disabled (redo after redesign settles)

## Ordering

Phases 1a, 1b, 1c are independent of each other.
Phase 1d depends on 1a.
Phase 2 depends on 1a and 1b.
Phase 3a/3b can be done before Phase 2 (temporarily breaks chain
verification, which is acceptable).
Phase 3c depends on Phase 2.
Phase 4 is last.
