# Stack-Based Encoding Plan

This document describes improvements to the proof trace
format and recording logic. The goals are to reduce **trace
size** and **merge tool performance** (memory and time). Recording
time performance is not a concern — the current recording
overhead is acceptable.

## Status

**A (stack refs)**: ✅ Implemented and committed.
**B (lazy T output)**: ✅ Implemented (uncommitted).
**C (peephole)**: ✅ Implemented (SPECL/SPECIALIZEL).
**Replayer/merge updates**: ❌ Not yet started.

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

## Three Improvements

The improvements are complementary.

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

Entries that are referenced from outside the stack window get
explicit IDs. Stack refs and explicit IDs can be freely mixed
within a single entry.

**P entries always carry their trace_id.** Theorem IDs are
kernel-assigned and always available. The `^k` notation saves
space only at *reference* sites (other entries pointing to a
theorem), not at the P entry itself. There are no anonymous
P entries — see "Design Decision" below.

### B. Lazy T Line Output (✅ done)

The intern map is maintained as today: every new term is
hashed, looked up, and inserted into the map. This ensures
proper dedup for the 52% of terms that are referenced
multiple times.

The change is: **the T line is not written at intern time.**
Instead, the T entry is pushed onto a buffer. The buffer is
flushed before each P entry is written:

- If all references to the term (from later buffer entries
  and from the upcoming P entry) are within stack depth →
  **write anonymous** (no ID in the output).
- Otherwise → **write with ID** (`T <id> ...`), as today.

Anonymous entries still push onto the replayer's term stack
and are reachable via `~k` references.

**Td fallback (late materialization):** If a term was written
anonymous but is later referenced by explicit ID (because a
far-away entry looked it up in the intern map), a `Td` line
is emitted: `Td <id> <kind> <args>`. Td defines the term by
ID without pushing onto the term stack, preserving stack sync
with the replayer. Anonymous sub-terms are recursively
materialised via Td first (bounded by term depth).

**Implementation:** Each intern map entry tracks a
`written_status ref` (UNWRITTEN | WRITTEN_ANON | WRITTEN_ID).
The T buffer is a list of `{id, status, term_refs,
render_body}` entries. `can_be_anonymous` scans later buffer
entries + external refs, counting intervening T entries to
verify stack positions.

**Scope:** The buffer spans a single proof step (terms
interned between consecutive P entries). Cross-step anonymous
entries would require buffering P entries, but P entries
cannot be anonymous (see below), so a wider window provides
diminishing returns.

### C. Peephole Optimisation (✅ done, partial)

Consecutive SPEC (or Specialize) entries where each uses the
previous result as its parent are collapsed into a single
SPECL (or SPECIALIZEL) compound entry. Mixed chains flush at
kind boundary.

**Implemented:**
- SPECL for SPEC chains
- SPECIALIZEL for Specialize chains

**Future candidates:**
- Iterated CONJUNCT1/CONJUNCT2 → indexed CONJUNCT
- INST_TYPE followed by INST → combined substitution
- Iterated AP_TERM / AP_THM

Compound rules reduce the number of P entries (fewer entries
for merge to track, fewer kernel calls at replay).

## Design Decision: No Anonymous P Entries

Unlike terms, theorems cannot be reconstructed from their
values — a `thm` is just hypotheses + conclusion, not the
derivation that produced it. There is no `dest_thm_derivation`
analogous to `dest_term`.

If a P entry were written anonymous and a later step
(outside the buffer window) referenced it by trace_id, there
would be no way to emit a `Pd` fallback line: we don't retain
the rule and arguments after the entry is written.

For terms, the `Td` fallback works because `dest_term` on the
intern map entry reconstructs the T line body. No such
mechanism exists for theorems.

Therefore: **P entries always carry their trace_id.** The
`^k` notation saves space at reference sites (86% of P-entry
references in numeralTheory use `^k`), which captures most
of the benefit.

**Merge tool optimisation:** When a theorem is only ever
referenced via `^k` (never by explicit ID anywhere in the
file), the merge tool knows it is purely local — no need for
a global ID, no cross-file dependency tracking, no entry in
offset/liveness tables. This gives the merge tool the memory
benefit of anonymous entries without requiring them in the
format. The 62% single-use-next theorems fall into this
category.

## New Format Elements

- `~k` — term stack reference (k = 0 for most recent)
- `^k` — theorem stack reference (k = 0 for most recent)
- T entry without leading ID — anonymous term, pushes onto
  term stack only, reachable only via `~k`
- `Td <id> <kind> <args>` — define a previously-anonymous
  term by explicit ID without pushing onto the stack
- `SPECL` / `SPECIALIZEL` — compound rules

**No `~` vs `~k` conflict:** In GEN_ABS, bare `~` (no digit
follows) means NONE. `~0`, `~1`, etc. (digit follows) are
stack refs. The parser distinguishes by lookahead.

## Empirical Results (numeralTheory)

After implementing A + C (stack refs + peephole):

| Metric | Value |
|--------|-------|
| T entries | 16,915 |
| P entries | 92,381 |
| `~k` term stack refs | 29,964 |
| `^k` theorem stack refs | 79,315 (86% of P refs) |
| SPECIALIZEL entries | 4,322 (mostly 4-arg = 3 collapsed) |
| SPECL entries | 64 |
| P entries eliminated by peephole | ~12,000 |

Phase B (lazy T output) expected to make ~47% of T entries
anonymous, based on single-use-within-8 data.

## Remaining Work

1. **Update replayer** (`ReplayTrace.sml`): parse `~k`/`^k`
   refs, maintain term/theorem stacks, handle anonymous T
   entries, implement SPECL/SPECIALIZEL replay, handle `Td`
   lines.
2. **Update merge tool** (`MergeTrace.sml`): handle `~k`/`^k`
   and SPECL/SPECIALIZEL in dep scanning; for ^k-only theorems
   skip global ID allocation; preserve stack encoding in
   merged output.
3. **Update TraceMetadata** (`TraceMetadata.sml`): handle
   SPECL/SPECIALIZEL and `~k`/`^k` tokens in `extract`.
4. **Measure lazy T impact**: run tracing build, count
   anonymous vs ID'd T entries, measure size reduction.
5. **Additional peephole patterns**: CONJUNCT indexing,
   combined INST_TYPE+INST, etc.
