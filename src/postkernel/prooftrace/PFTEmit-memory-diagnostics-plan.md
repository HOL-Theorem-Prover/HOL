# PFTEmit memory diagnostics: current understanding and next plan

Date: 2026-05-05

## Context

We are investigating high memory use/OOM risk in `PFTEmit.sml` when emitting Candle PFTs for large CakeML/HOL traces. Important constraints:

- Do **not** build in the assistant session. User runs builds/tests/replays manually.
- `PFTWriter` is streaming; it is not buffering all output commands.
- `PIntMap` is a Patricia tree, not a red-black tree.
- Existing correctness-sensitive fixes already verified/committed by user include capture-safe `Abs` binder reuse and local memoization in `pft_subst_tm` / `pft_rename_free`.
- Candle proforma improvements are committed. Temporary diagnostics used for
  this investigation are archived under
  `diagnostic-archive/2026-05-pftemit-memory/`; they are not present in the
  active `PFTEmit.sml`.

## Archived diagnostics

Applying `diagnostic-archive/2026-05-pftemit-memory/PFTEmit-diagnostics.patch`
to its recorded base makes `PFTEmit.sml` support `PFTEMIT_DIAG=1` with more
detailed logs.

New phase/memory diagnostics:

- `begin` line includes `rss_kb` and `hwm_kb` from `/proc/self/status`.
- `parsed heap_size=...` line after `parse` includes RSS/HWM.
- existing `walked`, large-export, and `summary` logs also include RSS/HWM.

New final summary counters:

- `fi_queries`
- `fi_misses`
- `fi_nonempty_fvs`
- `fi_total_fvs`
- `fi_max_fvs`
- `fi_nonempty_open_bvs`
- `fi_total_open_bvs`
- `fi_max_open_bvs`
- `tm_memo_hits`
- `tm_memo_misses`
- `tm_memo_sets`
- `th_memo_hits`
- `th_memo_misses`
- `th_memo_sets`
- `ty_memo_hits`
- `ty_memo_misses`
- `ty_memo_sets`

`diagnostic-archive/2026-05-pftemit-memory/diagnose-candle-emit.sh` is suitable
for stratified runs with the instrumentation patch applied. It:

- extracts theory list from `emit-candle-merged.sml`
- strips nested SML comments before extraction
- samples first/last/order-stratified/largest traces plus anchors
- runs serial `emit-one` jobs with `PFTEMIT_DIAG=1`
- removes existing per-theory `.candle.pft.bin` outputs before each run
- supports `TIMEOUT=...`
- now has `summarize LOGDIR` mode that emits CSV

Typical use:

```sh
DIAG=diagnostic-archive/2026-05-pftemit-memory/diagnose-candle-emit.sh
TIMEOUT=300 "$DIAG" run ./emit-candle-merged 60 diaglogs3 \
  > diaglogs3.run.log 2>&1
"$DIAG" summarize diaglogs3 > diaglogs3-summary.csv
```

## Current diaglogs3 status

The 60-theory sample completed. Evidence:

- `diaglogs3` has 60 `.log` files.
- no active `emit-candle-merged` / `diagnose-candle` process was found.
- `diaglogs3.run.log` ends with `DIAG_LOGDIR diaglogs3`.

## Key measurements from diaglogs3

### Phase memory examples

`riscv_step`:

```text
parsed RSS ~2.74GB, HWM ~4.73GB
walked RSS ~4.23GB
final RSS/HWM ~12.74GB
heap_size=43.7M
n_tm=332,899
n_th=30,857,703
th_memo_sets=17,415,504
tm_memo_sets=64,033
fi_misses=69,444
```

`bvl_constProof`:

```text
parsed RSS ~3.57GB, HWM ~4.94GB
walked RSS ~5.96GB
final RSS/HWM ~14.35GB
heap_size=55.7M
n_tm=4,551,396
n_th=42,872,809
th_memo_sets=15,537,137
tm_memo_sets=1,121,566
fi_misses=2,809,458
```

`clos_to_bvlProof`:

```text
parsed RSS ~2.36GB
walked RSS ~3.18GB
final RSS ~13.65GB, HWM ~16.30GB
heap_size=25.1M
n_tm=4,892,818
n_th=21,512,703
th_memo_sets=5,701,995
tm_memo_sets=695,694
fi_misses=1,153,665
```

`fromSexp`:

```text
parsed RSS ~1.92GB
walked RSS ~2.56GB
final RSS/HWM ~16.30GB
heap_size=19.0M
n_tm=698,088
n_th=15,635,726
th_memo_sets=7,043,791
tm_memo_sets=148,511
fi_misses=259,985
```

### Main conclusions

#### 1. Parsed heap / walk baseline is large, but not enough to explain final peak

Parse + walk can already be several GB, but emission state adds many more GB. Example: `riscv_step` grows from ~4.2GB after walk to ~12.7GB final.

#### 2. `th_memo` is a real suspect now

Actual measured `th_memo_sets` are huge:

```text
riscv_step       17.4M
bvl_constProof   15.5M
fromSexp          7.0M
mips_step         6.1M
arm_step          5.9M
```

Since `th_memo` is currently `int PIntMap.t ref`, millions of Patricia entries likely cost substantial memory. Earlier caution against blindly changing it was correct, but the measurements now justify testing a flat array.

Important: `th_memo_sets` is source trace theorem entries, not all synthetic Candle theorem IDs. Still very large.

#### 3. `tm_memo` is sparse relative to heap size

Current `tm_memo` is a heap-sized `int array`, but set counts are small relative to `heapSize`:

```text
riscv_step:      heap=43.7M, tm_memo_sets=64k
mips_step:       heap=17.4M, tm_memo_sets=83k
fromSexp:        heap=19.0M, tm_memo_sets=149k
bvl_constProof:  heap=55.7M, tm_memo_sets=1.12M
```

So `tm_memo` as a flat array is probably memory-wasteful. However, `tm_memo_hits` can be tens of millions, so replacing it with `PIntMap` may cost CPU. This should be tested separately.

#### 4. `fi_memo` is sometimes significant

`fi_misses` and stored set sizes are large in term-heavy theories:

```text
bvl_constProof: fi_misses=2.81M, fi_total_fvs=20.9M, fi_total_open_bvs=6.49M
balanced_map:   fi_misses=1.25M, fi_total_fvs=2.88M, fi_total_open_bvs=2.75M
pegComplete:    fi_misses=1.20M, fi_total_fvs=5.87M, fi_total_open_bvs=2.63M
clos_to_bvl:    fi_misses=1.15M, fi_total_fvs=4.56M, fi_total_open_bvs=2.50M
```

But `riscv_step` has only `fi_misses=69k`, so `fi_memo` is not the universal cause.

#### 5. `pft_fv_memo` remains tiny

`pft_fv_total_size` remains small even in high-RSS theories. It is not the main memory culprit.

#### 6. There are two memory regimes

- theorem-heavy/source-thm-heavy, term-light:
  - `riscv_step`, `mips_step`, `arm_step`
  - huge `th_memo_sets`, low `n_tm`, low `fi_misses`
- emitted-term-heavy / logical Cake proof theories:
  - `clos_to_bvlProof`, `closProps`, `bvl_constProof`, `pegComplete`, `balanced_map`
  - large `n_tm`, substantial term hash-cons metadata and `fi_memo`

#### 7. MLton HWM behavior matters

Many theories peak near ~16.3GB. Some final RSS is lower than HWM, e.g. `clos_to_bvlProof` final ~13.6GB but HWM ~16.3GB. Interpret `maxrss`/HWM as OOM risk, not exact final live set.

#### 8. Capture checking does lots of mostly-negative work

Examples:

```text
pegComplete:    would_capture_calls=3.54M, env_checks=26.9M, env_hits=1.3k
bvl_constProof: would_capture_calls=5.29M, env_checks=11.8M, env_hits=188
closProps:      would_capture_calls=8.83M, env_checks=9.64M, env_hits=1.6k
```

This suggests full `free_info` may be overpowered for common cases. Future redesign could use a targeted/negative capture predicate instead of storing full sets globally.

## Recommended next experiments

Do changes one at a time and have the user rebuild/rerun focused samples.

### Experiment 1: change `th_memo` from `PIntMap` to flat array

Current:

```sml
val th_memo : int PIntMap.t ref = ref PIntMap.empty
fun th_memo_get k = ... PIntMap.find ...
fun th_memo_set k v = th_memo := PIntMap.add k v (!th_memo)
```

Candidate:

```sml
val th_memo = Array.array(heapSize heap, ~1)
fun th_memo_get k = Array.sub(th_memo, k)
fun th_memo_set k v =
  (if diag andalso Array.sub(th_memo, k) < 0 then
     diag_th_memo_sets := !diag_th_memo_sets + 1
   else ();
   Array.update(th_memo, k, v))
```

Preserve hit/miss diagnostics in `th_memo_get`.

Expected effects:

- likely lower memory and faster lookup for theorem-heavy theories with millions of entries
- costs one heap-sized int array, so may be worse for tiny theories but acceptable
- especially promising for `riscv_step`, `bvl_constProof`, `fromSexp`, `mips_step`, `arm_step`

Focused rerun after user rebuilds:

```sh
PFTEMIT_DIAG=1 /usr/bin/time -v ./emit-candle-merged emit-one riscv_step
PFTEMIT_DIAG=1 /usr/bin/time -v ./emit-candle-merged emit-one bvl_constProof
PFTEMIT_DIAG=1 /usr/bin/time -v ./emit-candle-merged emit-one fromSexp
PFTEMIT_DIAG=1 /usr/bin/time -v ./emit-candle-merged emit-one mips_step
```

Compare `maxrss_kb`, phase RSS/HWM, elapsed, and final counters.

### Experiment 2: consider changing `tm_memo` from flat array to sparse map

Only after Experiment 1. Current data says the flat heap-sized `tm_memo` array is often sparse, but lookup traffic is high.

Candidate:

```sml
val tm_memo : int PIntMap.t ref = ref PIntMap.empty
```

with `find` returning `~1` on missing.

Risks:

- `tm_memo_hits` can be tens of millions, so CPU may regress.
- If memory win is small relative to CPU loss, revert.

Most useful test theories:

- `riscv_step` and `mips_step`: very sparse `tm_memo`, likely memory win
- `bvl_constProof` / `clos_to_bvlProof`: term-heavy, more realistic stress

### Experiment 3: investigate/rework `fi_memo`

This is more delicate and likely needs design work.

Options:

1. Sparse representation for `fi_memo` instead of heap-sized option array.
2. Avoid storing empty/common records aggressively.
3. Replace full `free_info` with targeted capture predicate/cache.
4. Cache negative capture answers keyed by binder `(name,type)` and heap body ptr.

Motivation: capture hits are extremely rare but current machinery computes/stores full free-variable/open-BV sets.

Do not start here unless `th_memo`/`tm_memo` experiments do not help enough, or if term-heavy theories remain problematic.

### Experiment 4: emitted term metadata audit

For theories with `n_tm` around 4--5M, retained emitted-term structures are likely major:

- `comb_ht`
- `abs_ht`
- `var_ht`
- `const_ht`
- `tm_part1`
- `tm_part2`
- `tm_types`
- `var_names`
- emitted-term `pft_fv_memo`

Possible future work:

- add per-table size diagnostics if cheap
- look for tables that can be compacted or avoided
- check whether some term metadata is only needed for derived-rule reconstruction and can be local/ephemeral

## Things not to prioritize now

- `PFTWriter` buffering: confirmed not relevant.
- `pft_fv_memo`: measured small.
- More `riscv_step` proforma-only work as a memory fix: proformas reduce output/work but did not materially reduce RSS in earlier tests.
- Blind `th_memo` changes without measuring: measurement is now done, and array experiment is justified.

## Useful commands for later analysis

Summarize existing logs:

```sh
diagnostic-archive/2026-05-pftemit-memory/diagnose-candle-emit.sh \
  summarize diaglogs3 > diaglogs3-summary.csv
```

Quick top-list script used by assistant:

```sh
python3 - <<'PY'
import csv
rows=[]
for r in csv.DictReader(open('diaglogs3-summary.csv')):
    def I(k):
        try: return int(r[k]) if r[k] else 0
        except Exception: return 0
    if I('heap_size'):
        r['_rss']=I('maxrss_kb'); r['_heap']=I('heap_size')
        r['_thsets']=I('th_memo_sets'); r['_tmsets']=I('tm_memo_sets')
        r['_fi']=I('fi_misses'); r['_n_tm']=I('n_tm'); r['_n_th']=I('n_th')
        rows.append(r)
for key,title in [('_rss','RSS'),('_heap','heap'),('_thsets','th_memo_sets'),
                  ('_tmsets','tm_memo_sets'),('_fi','fi_misses'),('_n_tm','n_tm'),('_n_th','n_th')]:
    print('\nTop',title)
    for r in sorted(rows,key=lambda x:x[key],reverse=True)[:10]:
        print(f"{r['theory']:24} rss={r['_rss']/1024:8.1f}MB heap={r['_heap']/1e6:6.1f} "
              f"thsets={r['_thsets']/1e6:6.1f} tmsets={r['_tmsets']/1e6:5.2f} "
              f"fi={r['_fi']/1e6:5.2f} n_tm={r['_n_tm']/1e6:5.2f} n_th={r['_n_th']/1e6:6.1f}")
PY
```

Inspect phase logs:

```sh
for t in riscv_step bvl_constProof clos_to_bvlProof fromSexp; do
  echo "--- $t"
  rg "PFTEmit\\[$t\\]: (begin|parsed|walked|summary)" diaglogs3/$t.log
done
```

## Current best plan

1. Implement `th_memo` as a flat array, keeping diagnostics.
2. User rebuilds and reruns focused theories.
3. If memory improves without problems, keep it.
4. Then test sparse `tm_memo` as a separate experiment.
5. If term-heavy theories remain near OOM, redesign `fi_memo` / capture analysis.
6. Later, audit emitted-term metadata for 4--5M-term theories.
