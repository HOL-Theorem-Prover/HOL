# Stack-Based Encoding Plan

This document describes improvements to the proof trace
format and recording logic. The goals are to reduce **trace
size** and **merge tool performance** (memory and time). Recording
time performance is not a concern — the current recording
overhead is acceptable.

## Status

**A (stack refs)**: ✅ Implemented and committed.
**B (peephole)**: ✅ Implemented and committed.
**Anonymous T entries / Td**: ❌ Tried and rejected (see below).

## Motivation

Empirical data from CakeML backend traces (wordPropsTheory,
50M P entries):

- 78.7% of theorems are referenced exactly once
- 62% of all theorems are used once, by the very next P entry
- 47% of terms are referenced once, within 8 lines
- 52% of terms are referenced multiple times (shared)
- Dominant single-use-next rules: Specialize (43K/200K),
  AP_TERM (18K), SPEC (14K), INST_TYPE (11K)

Currently every T and P entry gets an explicit integer ID,
and every reference uses that ID. For single-use intermediates,
the IDs are written once, referenced once, and contribute to
both trace size and merge tool memory pressure (byte offsets,
dependency arrays, liveness tracking). The trace format can be
made substantially more compact by exploiting the fact that
most entries are consumed by nearby entries.

## Two Improvements

### A. Stack-Based References (✅ done)

Both terms and theorems maintain implicit stacks of depth 16.
The term stack is the sequence of T entries in output order.
The theorem stack is the sequence of P entries in output order.
Stack positions are relative: `~0` is the most recently
written T entry, `~1` the one before, etc. `^0` is the most
recently written P entry, `^1` the one before, etc.

**Today:**
```
T 4500 V x ty3
T 4501 C foo bar ty5
T 4502 A 4501 4500
P 985430 SPEC 985429 4502
P 985431 SPEC 985430 4500
P 985432 TRANS 985431 985428
```

**With stack encoding:**
```
T 4500 V x ty3
T 4501 C foo bar ty5
T 4502 A ~0 ~1
P 985430 SPEC 985429 ~0
P 985431 SPEC ^0 ~1
P 985432 TRANS ^0 985428
```

The replayer maintains matching stacks and resolves `~k`/`^k`
to actual term/theorem values.

Every T entry carries an explicit ID. Every P entry carries
its trace_id. Stack refs and explicit IDs can be freely mixed
at reference sites within a single entry.

### B. Peephole Optimisation (✅ done)

Consecutive SPEC (or Specialize) entries where each uses the
previous result as its parent are collapsed into a single
SPECL (or SPECIALIZEL) compound entry. Mixed chains flush at
kind boundary.

A `spec_chain` accumulator tracks the current chain. It is
flushed when a non-matching entry arrives, or at close/export
time.

**Implemented:**
- SPECL for SPEC chains
- SPECIALIZEL for Specialize chains

**Future candidates:**
- Iterated CONJUNCT1/CONJUNCT2 → indexed CONJUNCT
- INST_TYPE followed by INST → combined substitution
- Iterated AP_TERM / AP_THM

## Design Decision: No Anonymous T Entries

An earlier design deferred T line output to a buffer and wrote
some T entries without IDs ("anonymous"), using `Td` lines for
late materialisation when anonymous terms were later referenced
by explicit ID. This was tried and rejected:

1. **High fallback rate**: With a per-step buffer, 61% of
   anonymous T entries in numeralTheory needed Td fallback.
   A wider buffer (unified T/P buffer) would reduce this but
   adds significant implementation complexity.

2. **Format complexity**: Anonymous T entries required 8 extra
   grammar productions (4 anonymous T + 4 Td). The replayer
   and merge tool would need to handle both forms plus Td,
   plus maintain `written_status` tracking.

3. **Marginal benefit over ~k refs**: Anonymous entries save
   a few digits per T entry (the ID field). But `~k` refs
   already save digits at every *reference* site, and there
   are typically more references than definitions. The
   marginal benefit of omitting IDs from definitions is small.

4. **Merge tool doesn't need anonymous entries**: The merge
   tool can detect `~k`-only terms (terms whose ID never
   appears at a reference site) by scanning reference sites
   during the dep pass. These terms are purely local and
   don't need global IDs, dedup, or offset tracking —
   regardless of whether the T entry carries an ID in the
   trace. The same applies to `^k`-only theorems.

Therefore: every T entry carries an explicit ID, every P entry
carries its trace_id. The recording logic writes T and P lines
immediately (no buffering). The `~k`/`^k` notation captures
the locality benefit at reference sites.

## Merge Tool Optimisations

The stack encoding enables two merge tool optimisations that
don't require format changes:

**`^k`-only theorems**: If a theorem's trace_id never appears
as an explicit ID at any reference site in the file (all
references use `^k`), the merge tool knows it is purely local.
No global ID allocation, no cross-file dependency tracking,
no entry in offset/liveness tables. ~62% of theorems fall
into this category.

**`~k`-only terms**: If a term's ID never appears as an
explicit ID at any reference site (all references use `~k`),
the merge tool can skip global ID allocation and dedup for
that term. ~47% of terms fall into this category.

Both are detected by scanning reference sites during the dep
pass — a simple check with no format or recording changes.

## Format Elements

- `~k` — term stack reference (k = 0 for most recent)
- `^k` — theorem stack reference (k = 0 for most recent)
- `SPECL` / `SPECIALIZEL` — compound rules

**No `~` vs `~k` conflict:** In GEN_ABS, bare `~` (no digit
follows) means NONE. `~0`, `~1`, etc. (digit follows) are
stack refs. The parser distinguishes by lookahead.

## Empirical Results (numeralTheory)

| Metric | Value |
|--------|-------|
| T entries | 16,915 |
| P entries | 92,381 |
| `~k` term stack refs | 29,964 |
| `^k` theorem stack refs | 79,315 (86% of P refs) |
| SPECIALIZEL entries | 4,322 (mostly 4-arg = 3 collapsed) |
| SPECL entries | 64 |
| P entries eliminated by peephole | ~12,000 |

## Remaining Work

1. **Update replayer** (`ReplayTrace.sml`): parse `~k`/`^k`
   refs, maintain term/theorem stacks, implement
   SPECL/SPECIALIZEL replay.
2. **Update merge tool** (`MergeTrace.sml`): handle `~k`/`^k`
   and SPECL/SPECIALIZEL in dep scanning; for `^k`-only
   theorems skip global ID allocation; for `~k`-only terms
   skip global ID allocation and dedup; preserve stack
   encoding in merged output.
3. **Update TraceMetadata** (`TraceMetadata.sml`): handle
   SPECL/SPECIALIZEL and `~k`/`^k` tokens in `extract`.
4. **Additional peephole patterns**: CONJUNCT indexing,
   combined INST_TYPE+INST, etc.
