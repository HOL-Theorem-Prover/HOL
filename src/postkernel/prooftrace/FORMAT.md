# HOL4 Proof Trace Format (`.pftrace`)

Version 1. Produced by `TraceRecord` + `TraceExport` (stdknl with `HOL_TRACE_PROOFS=1`).
Verified by `ReplayTrace`.

## Overview

A `.pftrace` file records every kernel inference step needed to derive
a theory's exported theorems. Files are typically compressed (`.pftrace.zst`
or `.pftrace.gz`). Each file is self-contained: it includes type, term,
and proof step tables, plus an export list mapping theorem names to steps.

Per-theory traces are build intermediates. A merge tool combines them into
a single self-contained trace for from-scratch replay.

## Grammar

```
trace    ::= header types terms steps exports

header   ::= "HOL4_PROOF_TRACE " version "\n"
             "THEORY " name "\n"
             "COUNTS " n_types " " n_terms " " n_steps "\n"

types    ::= type_entry*
type_entry ::= "Y " id " V " name "\n"           (* type variable *)
             | "Y " id " O " thy name argid* "\n" (* type operator *)

terms    ::= term_entry*
term_entry ::= "M " id " V " name tyid "\n"       (* variable *)
             | "M " id " C " thy name tyid "\n"    (* constant *)
             | "M " id " A " fid xid "\n"          (* application *)
             | "M " id " L " vid bid "\n"           (* lambda *)

steps    ::= step_entry*
step_entry ::= "P " id " " rule operands (" | " parentid*)? "\n"

exports  ::= export_entry*
export_entry ::= "E " name " " stepid "\n"
```

Sections are separated by blank lines.

## Fields

- **version**: integer, currently `1`
- **name**: unquoted token or quoted string (`"..."` with `\"`, `\\`, `\n`, `\xNN` escapes)
- **id**, **argid**, **tyid**, **fid**, **xid**, **vid**, **bid**, **stepid**, **parentid**: non-negative integers
- **n_types**, **n_terms**, **n_steps**: array dimensions (actual entries may be fewer after pruning)

## Inference Rules

Each step records one kernel inference rule. Parent IDs (after `|`) reference
earlier steps that produced the input theorems.

| Rule | Operands | Parents | Kernel function |
|------|----------|---------|----------------|
| `REFL` | `term_id` | — | `Thm.REFL` |
| `ASSUME` | `term_id` | — | `Thm.ASSUME` |
| `BETA_CONV` | `term_id` | — | `Thm.BETA_CONV` |
| `ALPHA` | `term_id` `term_id` | — | `Thm.ALPHA` |
| `ABS` | `var_id` | 1 | `Thm.ABS` |
| `MK_COMB` | — | 2 | `Thm.MK_COMB` |
| `AP_TERM` | `term_id` | 1 | `Thm.AP_TERM` |
| `AP_THM` | `term_id` | 1 | `Thm.AP_THM` |
| `SYM` | — | 1 | `Thm.SYM` |
| `TRANS` | — | 2 | `Thm.TRANS` |
| `EQ_MP` | — | 2 | `Thm.EQ_MP` |
| `EQ_IMP_RULE1` | — | 1 | `#1 (Thm.EQ_IMP_RULE)` |
| `EQ_IMP_RULE2` | — | 1 | `#2 (Thm.EQ_IMP_RULE)` |
| `MP` | — | 2 | `Thm.MP` |
| `DISCH` | `term_id` | 1 | `Thm.DISCH` |
| `INST_TYPE` | `n` (`tyvar_id` `type_id`){n} | 1 | `Thm.INST_TYPE` |
| `INST` | `n` (`var_id` `term_id`){n} | 1 | `Thm.INST` |
| `SUBST` | `n` `var_id`{n} `template_id` | n+1 | `Thm.SUBST` |
| `SPEC` | `term_id` | 1 | `Thm.SPEC` |
| `Specialize` | `term_id` | 1 | `Thm.Specialize` (lazy-beta SPEC) |
| `GEN` | `var_id` | 1 | `Thm.GEN` |
| `GENL` | `n` `var_id*` | 1 | `Thm.GENL` |
| `GEN_ABS` | `opt_cst_id` `n` `var_id*` | 1 | `Thm.GEN_ABS` |
| `EXISTS` | `existential_id` `witness_id` | 1 | `Thm.EXISTS` |
| `CHOOSE` | `var_id` | 2 | `Thm.CHOOSE` |
| `CONJ` | — | 2 | `Thm.CONJ` |
| `CONJUNCT1` | — | 1 | `Thm.CONJUNCT1` |
| `CONJUNCT2` | — | 1 | `Thm.CONJUNCT2` |
| `DISJ1` | `term_id` | 1 | `Thm.DISJ1` |
| `DISJ2` | `term_id` | 1 | `Thm.DISJ2` |
| `DISJ_CASES` | — | 3 | `Thm.DISJ_CASES` |
| `NOT_INTRO` | — | 1 | `Thm.NOT_INTRO` |
| `NOT_ELIM` | — | 1 | `Thm.NOT_ELIM` |
| `CCONTR` | `term_id` | 1 | `Thm.CCONTR` |
| `Beta` | — | 1 | `Thm.Beta` (compute-optimized right-beta) |
| `Mk_comb` | — | 3 | `Thm.Mk_comb` |
| `Mk_abs` | — | 2 | `Thm.Mk_abs` |
| `DEF_TYOP` | `thy` `name` `concl_id` | 1 | `Thm.prim_type_definition` (conservative type definition) |
| `DEF_SPEC` | `thyname` `n` `cname*` `concl_id` | 1 | `Thm.prim_specification` / `gen_prim_specification` (conservative constant specification) |
| `COMPUTE_INIT` | `n_cval` (`name` `term_id`){n_cval} `cval_type_id` `num_type_id` `n_char` `char_name`{n_char} | n_char | `Thm.compute` initialization (once per trace) |
| `COMPUTE` | `input_term_id` | 0+ | `Thm.compute` evaluation; parents are code equation thms |

### Trust Steps

These represent the trust boundary of a trace file.

| Rule | Operands | Parents | Meaning |
|------|----------|---------|---------|
| `AXIOM` | `concl_id` | — | Axiom introduction |
| `ORACLE` | `tag` ... | — | Oracle theorem |

`ORACLE` format depends on the tag:
- `ORACLE DISK_THM <theory> <name>`: ancestor theorem reference (per-theory traces only; replaced by direct step references in merged traces)
- `ORACLE <tag> <concl_id> <nhyps> <hyp_ids*>`: other oracle theorems (SAT solver, etc.)

## Semantics

- **IDs are dense** within each section after pruning (dead entries omitted).
  COUNTS declares array dimensions (upper bound).
- **Types and terms** are in topological order: sub-components have smaller IDs.
- **Steps** may reference types, terms, and earlier steps. Parent IDs after `|`.
- **SUBST** parent order: the first `n` parents are the residue theorems
  (corresponding to the `n` variable IDs in the operands), followed by the
  original theorem as the last parent.
- **Mk_comb** parents: parent 0 is the original equality theorem
  (`A |- t = u v`), parents 1 and 2 are the function and argument
  sub-results (`A' |- u = u'` and `A'' |- v = v'`).
- **Mk_abs** parents: parent 0 is the original equality theorem
  (`A |- t = \x.u`), parent 1 is the body sub-result (`A' |- u = u'`).
- **COMPUTE_INIT** must appear at most once, before any `COMPUTE` steps.
  It records the initialization arguments for `Thm.compute`.
- **COMPUTE** steps use the closure established by `COMPUTE_INIT`.
  The code equation thms are in the parent list.
- **Exports** map theorem names to step IDs. These are the theory's public API.

## Verification

A merged trace is verified by:
1. Building type and term arrays from Y/M entries
2. Replaying each step through the actual kernel inference rules
3. Checking each export's replayed conclusion matches the expected theorem

Per-theory traces can also be replayed individually, but `ORACLE DISK_THM`
entries will remain as oracle-tagged theorems unless resolved by a merge tool.

## Compression

Files are typically stored as `.pftrace.zst` (preferred) or `.pftrace.gz`.
The replayer auto-detects format from extension.
