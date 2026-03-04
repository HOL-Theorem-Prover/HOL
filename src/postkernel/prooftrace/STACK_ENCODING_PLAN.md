# Stack-Based Encoding Plan

This document describes planned improvements to the proof trace
format and recording logic. The goals are to reduce **trace
size** and **merge tool performance** (memory and time). Recording
time performance is not a concern — the current recording
overhead is acceptable.

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

The improvements are complementary and share a common
implementation mechanism (the entry buffer).

### A. Stack-Based References

Both terms and theorems maintain implicit stacks. The term
stack is the sequence of T entries in output order. The
theorem stack is the sequence of P entries in output order.
Stack positions are relative: `~0` is the most recently
written T entry, `~1` the one before, etc. `^0` is the most
recently written P entry, `^1` the one before, etc.

Entries referenced only via stack positions don't need an
explicit ID in the trace output.

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
T V x ty3
T C foo bar ty5
T A ~0 ~1
P SPEC 985429 ~0
P SPEC ^0 ~1
P TRANS ^0 985428
```

The replayer maintains matching stacks and resolves `~k`/`^k`
to actual term/theorem values.

Entries that are referenced from outside the stack window get
explicit IDs (as today). The number of references doesn't
matter — only whether all references are within stack depth.
Stack refs and explicit IDs can be freely mixed within a
single entry.

The stack depth is bounded (e.g., 8 or 16 for each of the
term and theorem stacks). References beyond the stack depth
use explicit IDs.

**Theorem IDs vs stack refs:** Theorem IDs (trace_ids) are
assigned by the kernel and are already present on the thm
object — they're free. The theorem stack doesn't save any
recording-time computation. Its value is purely in trace
compactness: `^0` is shorter than a multi-digit trace_id,
and anonymous P entries omit the result ID entirely. For
theorems, IDs are always available (the kernel assigns them
regardless); the question is just whether to print them.

### B. Lazy T Line Output

The intern map is maintained as today: every new term is
hashed, looked up, and inserted into the map. This ensures
proper dedup for the 52% of terms that are referenced
multiple times (possibly by different ML objects for the same
mathematical term).

The change is: **the T line is not written at intern time.**
Instead, the T entry is pushed onto the term stack in the
buffer. The T line is written only when the entry is flushed
from the buffer:

- If all references to the term are within stack depth →
  **write anonymous** (no ID in the output). The trace is
  shorter, and the merge tool has one fewer entry to track.
- If the term is referenced from outside the stack window →
  **write with ID** (`T <id> ...`), as today.

When a term is evicted from the stack (falls off the bottom),
it's already in the intern map (so future encounters dedup
correctly). If the term was written anonymous but is later
referenced by ID (because a far-away entry looked it up in
the intern map), the T line with the ID is written at that
point — just before the entry that needs it.

**Flow:**
1. `intern_term(t)` is called (for a P entry's argument):
   - Pointer-eq cache hit → return existing ID
   - Pointer-eq scan of term stack → return `~k`
   - Map lookup → hit: return ID. If T line for this ID has
     not been written yet, **write it now** (lazy output).
   - Map miss → assign new ID, insert into map and cache,
     push T entry to buffer, mark as "not yet written"
2. Buffer the P entry
3. On flush: for each T entry, decide anonymous vs ID'd
   based on whether all references are stack-reachable

This preserves correctness (the intern map deduplicates as
today) while reducing trace output (47% of T entries become
anonymous — no IDs, no T line with an ID written).

**Lazy write detail:** Each intern map entry tracks whether
its T line has been written. When a term is first interned,
its T line is deferred (marked unwritten). The T line is
written in one of two cases:
- The entry is flushed from the buffer with references
  outside the stack window → write `T <id> ...`
- A later `intern_term` call looks up the same term in the
  map and finds the T line unwritten → write `T <id> ...`
  now, before the P entry that triggered this lookup

In both cases, the T line appears in the trace before any
entry that references the term by ID. Dependency order is
preserved.

### C. Peephole Optimisation

The buffer enables pattern recognition before flushing.
Common multi-step patterns are collapsed into compound rules.

**SPECL** (chain of SPEC / Specialize):
```
Before:  P SPEC ^0 ~2
         P SPEC ^0 ~1
         P SPEC ^0 ~0
After:   P SPECL ^2 ~2 ~1 ~0
```

**Other candidates:**
- Iterated CONJUNCT1/CONJUNCT2 (extracting from nested
  conjunctions) → indexed CONJUNCT
- INST_TYPE followed by INST → combined substitution
- Iterated AP_TERM / AP_THM (building applications)

Compound rules reduce the number of P entries (fewer entries
for merge to track, fewer kernel calls at replay), and the
terms involved become arguments to a single entry rather than
separate entries with separate IDs.

SPECL already exists in the HOL kernel. Other compounds may
need new replay-side implementations (but these are just
derived rules — no kernel changes needed for soundness).

## The Entry Buffer

The buffer is the shared mechanism for all three improvements.

**Structure:** A circular buffer of the last N entries (T and
P intermixed, in output order). N should be at least the stack
depth (e.g., 16).

**Recording flow:**
1. Kernel rule fires (e.g., SPEC(thm, term))
2. Recorder calls `intern_term(term)`:
   - Intern sub-terms recursively (each may hit cache, stack,
     or be pushed to buffer)
   - Push outer term to buffer
3. Recorder pushes P entry to buffer
4. If buffer is full, flush oldest entries:
   a. Check for peephole patterns (C)
   b. For each T entry: if all its references are within
      stack depth, write anonymous; otherwise write with
      ID (B)
   c. Write entries with stack refs where applicable (A)
   d. For T entries written with ID, mark as "written" in
      the intern map

**Flush ordering:** T entries are written before the P entries
that reference them (preserving dependency order). Within the
buffer, entries are flushed in order.

**Replay flow:**
1. Replayer maintains a term stack and theorem stack (circular
   buffers of the same depth)
2. On `T` with no ID: construct term, push onto term stack
3. On `T <id>`: construct term, store by ID AND push onto
   term stack
4. On `P` with no ID: execute rule, push onto theorem stack
5. On `P <id>`: execute rule, store by ID AND push onto
   theorem stack
6. Resolve `~k` / `^k` by indexing into the appropriate stack

## Expected Impact

Based on wordPropsTheory (50M P entries, representative of
large CakeML backend proofs):

| Metric | Today | With improvements |
|--------|-------|-------------------|
| T entries with IDs | 100% | ~53% |
| P entries with IDs | 100% | ~38% (est.) |
| Total entry count | baseline | reduced by peephole |
| Trace size | baseline | ~30-40% smaller (est.) |

The trace size reduction comes from: no IDs on anonymous
entries, short stack refs (`^0` vs multi-digit IDs), fewer
T lines with IDs, and collapsed compound rules.

The merge tool benefits from smaller traces (less to
decompress and parse) and fewer distinct entries (less
memory for byte offsets, dependency arrays, and liveness
tracking).

Recording time must not regress from the status quo (which
is acceptable). This proposal is at worst neutral: the intern
map is maintained exactly as today (same hash, lookup, insert),
with a small buffer and lazy output logic added. The buffer
adds minor bookkeeping, but the actual I/O is reduced (fewer
T lines written, shorter references), so the net effect should
be at worst status quo and likely slightly better.

## Format Changes

The stack encoding requires a format version bump (the
replayer must understand `~k` and `^k` references and
anonymous entries).

**New syntax elements:**
- `^k` — theorem stack reference (k = 0 for most recent)
- `~k` — term stack reference (k = 0 for most recent)
- T entry without leading ID — anonymous, pushes onto term
  stack only
- P entry without leading ID — anonymous, pushes onto
  theorem stack only
- `SPECL` and other compound rules

**Backward compatibility:** The merge tool and replayer need
updating. Old-format traces (explicit IDs everywhere) remain
valid — they just don't use stack refs. A version number in
the V line distinguishes formats.

## Implementation Order

1. **Buffer infrastructure** in TraceRecord: circular buffer
   of entries, flush logic, no stack refs yet (just buffer
   and flush in order — should be a no-op refactor)

2. **Term stack** (A + B for terms): `~k` references in T
   and P entries, anonymous T entries, lazy T line output.
   This is the main win (47% of T entries become anonymous).

3. **Theorem stack** (A for theorems): `^k` references in
   P entries, anonymous P entries. Modest trace size win.

4. **Peephole** (C): SPECL and other compound rules. Can be
   added incrementally, one pattern at a time.

5. **Replayer updates**: resolve `~k`/`^k`, handle anonymous
   entries, implement compound rules.

6. **Merge tool updates**: handle new format in both passes.

Steps 1-3 can be tested independently (correct traces, just
more compact). Step 4 is incremental on top.

## Open Questions

- Optimal stack/buffer depth? 8 and 16 both capture most
  single-use entries. Larger depth = more pointer-eq scans
  per intern call but higher hit rate. Worth benchmarking.

- Should types (Y entries) also use a stack? Types are fewer
  and smaller — the benefit may not justify the complexity.
  Current data: Y entries are ~1% of lines.

- Interaction with compression: stack encoding reduces
  redundancy in the uncompressed text, but compressed size
  may not shrink as much (the compressor already exploits
  the redundancy in repeated ID patterns). The main win is
  trace size before compression and merge tool entry count.

- Merge tool implications: the merge tool currently reads
  entries and remaps IDs. With stack encoding, it needs to
  either (a) maintain stacks during reading and resolve
  refs, then re-encode with stacks during writing, or
  (b) resolve all stack refs to explicit IDs during pass 1
  and use the simpler explicit-ID format for the merged
  output. Option (b) is simpler initially.
