# HOL4 Proof Trace Format (`.pftrace`)

Version 1. Produced by `TraceRecord` + `TraceExport` (stdknl with `HOL_TRACE_PROOFS=1`).
Verified by `ReplayTrace`.

## Overview

A `.pftrace` file records every kernel inference step needed to derive
a theory's exported theorems. Files are typically compressed (`.pftrace.zst`
or `.pftrace.gz`). Each file is self-contained: it includes type, term,
and proof step tables, plus an export list mapping theorem names to steps.

## Grammar

```
trace    ::= header types terms steps exports

header   ::= "HOL4_PROOF_TRACE " version "\n"
             "THEORY " name "\n"
             "PARENTS " name* "\n"
             ("ANCESTOR " name " sha256:" hexdigest "\n")*
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
- **hexdigest**: 64 hex characters (SHA-256 of ancestor `.pftrace.zst` or `.gz`)
- **n_types**, **n_terms**, **n_steps**: array dimensions (actual entries may be fewer after pruning)

## Inference Rules

Each step records one kernel inference rule. Parent IDs (after `|`) reference
earlier steps that produced the input theorems.

| Rule | Operands | Parents | Kernel function |
|------|----------|---------|----------------|
| `REFL` | `term_id` | — | `Thm.REFL` |
| `ASSUME` | `term_id` | — | `Thm.ASSUME` |
| `BETA_CONV` | `term_id` | — | `Thm.BETA_CONV` |
| `MK_COMB` | — | 2 | `Thm.MK_COMB` |
| `ABS` | `var_id` | 1 | `Thm.ABS` |
| `MP` | — | 2 | `Thm.MP` |
| `DISCH` | `term_id` | 1 | `Thm.DISCH` |
| `DEDUCT_ANTISYM` | — | 2 | `Thm.DEDUCT_ANTISYM_RULE` |
| `EQ_MP` | — | 2 | `Thm.EQ_MP` |
| `INST_TYPE` | `n` (`tyvar_id` `type_id`){n} | 1 | `Thm.INST_TYPE` |
| `INST` | `n` (`var_id` `term_id`){n} | 1 | `Thm.INST` |
| `SUBST` | `n` (`hvar_id` `thm_parent`){n} `template_id` | 1+ | `Thm.SUBST` |
| `Mk_abs` | `bvar_id` | 1 | internal: `Thm.Mk_abs` |
| `Mk_comb` | — | 2 | internal: `Thm.Mk_comb` |
| `SYM` | — | 1 | `Thm.SYM` |
| `TRANS` | — | 2 | `Thm.TRANS` |
| `AP_THM` | `term_id` | 1 | `Thm.AP_THM` |
| `AP_TERM` | `term_id` | 1 | `Thm.AP_TERM` |
| `ALPHA` | `term_id` `term_id` | — | `Thm.ALPHA` |
| `GEN_ABS` | `opt_cst_id` `n` `var_id*` | 1 | `Thm.GEN_ABS` |
| `NOT_INTRO` | — | 1 | `Thm.NOT_INTRO` |
| `NOT_ELIM` | — | 1 | `Thm.NOT_ELIM` |
| `CCONTR` | `term_id` | 1 | `Thm.CCONTR` |
| `EXISTS` | `existential_id` `witness_id` | 1 | `Thm.EXISTS` |
| `CHOOSE` | `var_id` | 2 | `Thm.CHOOSE` |
| `CONJ` | — | 2 | `Thm.CONJ` |
| `CONJUNCT1` | — | 1 | `Thm.CONJUNCT1` |
| `CONJUNCT2` | — | 1 | `Thm.CONJUNCT2` |
| `DISJ1` | `term_id` | 1 | `Thm.DISJ1` |
| `DISJ2` | `term_id` | 1 | `Thm.DISJ2` |
| `DISJ_CASES` | — | 3 | `Thm.DISJ_CASES` |
| `SPEC` | `term_id` | 1 | `Thm.SPEC` |
| `GEN` | `var_id` | 1 | `Thm.GEN` |
| `GENL` | `n` `var_id*` | 1 | `Thm.GENL` |
| `ADD_ASSUM` | `term_id` | 1 | `Thm.ADD_ASSUM` |

### Opaque Steps

These record their theorem statement (conclusion + hypotheses) rather than
being replayed through the kernel.

| Rule | Operands | Parents | Meaning |
|------|----------|---------|---------|
| `AXIOM` | `concl_id` | — | Axiom introduction |
| `ORACLE` | `tag` `concl_id` `nhyps` `hyp_ids*` | — | Oracle theorem |
| `DISK_THM` | `concl_id` `nhyps` `hyp_ids*` | — | Loaded from disk |
| `TRUST` | `global_id` [`thy_name`] `concl_id` `nhyps` `hyp_ids*` | — | Ancestor theorem |
| `DEF_TYOP` | `thy` `name` `concl_id` | 1 | Type definition |
| `DEF_SPEC` | `concl_id` | 1 | Constant specification |
| `COMPUTE` | `input_id` `result_id` | — | Computation (trusted) |

## Semantics

- **IDs are dense** within each section after pruning (dead entries omitted).
  COUNTS declares array dimensions (upper bound).
- **Types and terms** are in topological order: sub-components have smaller IDs.
- **Steps** may reference types, terms, and earlier steps. Parent IDs after `|`.
- **TRUST** entries represent theorems from ancestor theories. During chain
  verification, these are resolved against actually-replayed ancestor exports.
- **COMPUTE** entries record `input ⊢ input = result`. A verifier may
  independently evaluate the input term to check the equation.
- **Exports** map theorem names to step IDs. These are the theory's public API.

## Verification

A trace is verified by:
1. Building type and term arrays from Y/M entries
2. Replaying each step through the actual kernel inference rules
3. Checking each export's replayed conclusion matches the theory's theorem

Chain verification replays an entire theory dependency graph bottom-up,
using replayed ancestor exports to resolve TRUST entries.

## Compression

Files are typically stored as `.pftrace.zst` (preferred) or `.pftrace.gz`.
The replayer auto-detects format from extension.
