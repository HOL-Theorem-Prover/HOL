#!/usr/bin/env bash
set -euo pipefail

# Lightweight diagnostics runner for Candle PFT emission.
#
# Usage:
#   ./diagnose-candle-emit.sh list [N]
#   ./diagnose-candle-emit.sh run ./emit-candle-merged [N] [LOGDIR]
#   ./diagnose-candle-emit.sh summarize LOGDIR
#
# N defaults to 60.  The sample is stratified by theory order and by
# *Theory.tr.gz size: first/last windows, regularly-spaced order points, and
# largest traces.  Runs are serial emit-one jobs with PFTEMIT_DIAG=1.

MODE=${1:-list}
if [[ "$MODE" == "list" ]]; then
  EXE=./emit-candle-merged
  N=${2:-60}
  LOGDIR=${3:-emit-diagnostics-$(date +%Y%m%d-%H%M%S)}
elif [[ "$MODE" == "summarize" ]]; then
  EXE=./emit-candle-merged
  N=60
  LOGDIR=${2:-diaglogs}
else
  EXE=${2:-./emit-candle-merged}
  N=${3:-60}
  LOGDIR=${4:-emit-diagnostics-$(date +%Y%m%d-%H%M%S)}
fi
DRIVER=${DRIVER:-emit-candle-merged.sml}
TIMEOUT=${TIMEOUT:-}
TIME=${TIME:-/usr/bin/time}

make_sample() {
python3 - "$DRIVER" "$N" <<'PY'
import os, re, sys
path = sys.argv[1]
limit = int(sys.argv[2])
s = open(path).read()

def strip_sml_comments(src):
    # Remove nested SML comments: (* ... *)
    out = []
    i = 0
    depth = 0
    n = len(src)
    while i < n:
        if i + 1 < n and src[i:i+2] == '(*':
            depth += 1
            i += 2
        elif depth > 0 and i + 1 < n and src[i:i+2] == '*)':
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(src[i])
            i += 1
    return ''.join(out)

s = strip_sml_comments(s)

def list_body(name):
    m = re.search(r"val\s+" + re.escape(name) + r"\s*=\s*\[(.*?)\]\s*\n\nval\s+", s, re.S)
    if not m:
        raise SystemExit(f"could not find {name}")
    return m.group(1)

def strings(body):
    return re.findall(r'"([^"\\]*(?:\\.[^"\\]*)*)"', body)

ths = strings(list_body("till_cv_theories")) + strings(list_body("after_cv_theories"))
# Preserve order, remove duplicates caused by repeated set_sep/byte/etc.
seen = set(); ordered = []
for t in ths:
    if t not in seen:
        seen.add(t); ordered.append(t)

n = len(ordered)
want = []
def add(t):
    if t in seen and t not in want:
        want.append(t)

# order-stratified windows
for i in range(min(10, n)): add(ordered[i])
for i in range(max(0, n-10), n): add(ordered[i])
# evenly spaced order points
slots = max(1, limit // 2)
for k in range(slots):
    idx = round(k * (n - 1) / max(1, slots - 1))
    add(ordered[idx])
# largest traces by compressed size
sizes = []
for t in ordered:
    fn = f"{t}Theory.tr.gz"
    if os.path.exists(fn):
        sizes.append((os.path.getsize(fn), t))
for _, t in sorted(sizes, reverse=True)[:max(10, limit // 3)]:
    add(t)
# known/suspected useful anchors
for t in ["ast", "semanticPrimitives", "evaluate", "semanticPrimitivesProps",
          "closSem", "bvlSem", "bviSem", "parserProof", "typeSystem"]:
    add(t)

for t in want[:limit]:
    fn = f"{t}Theory.tr.gz"
    sz = os.path.getsize(fn) if os.path.exists(fn) else -1
    print(f"{t}\t{sz}")
PY
}

case "$MODE" in
  list)
    make_sample
    ;;
  run)
    mkdir -p "$LOGDIR"
    make_sample | while IFS=$'\t' read -r thy bytes; do
      out="${thy}.candle.pft.bin"
      log="$LOGDIR/${thy}.log"
      echo "DIAG_START theory=$thy trace_bytes=$bytes log=$log"
      rm -f "$out"
      if [[ -n "$TIMEOUT" ]]; then
        cmd=(timeout "$TIMEOUT" "$EXE" emit-one "$thy")
      else
        cmd=("$EXE" emit-one "$thy")
      fi
      set +e
      PFTEMIT_DIAG=1 PFTEMIT_DIAG_LARGE_TM=${PFTEMIT_DIAG_LARGE_TM:-50000} \
      PFTEMIT_DIAG_LARGE_TH=${PFTEMIT_DIAG_LARGE_TH:-50000} \
        "$TIME" -v "${cmd[@]}" >"$log" 2>&1
      st=$?
      set -e
      out_bytes=-1
      [[ -f "$out" ]] && out_bytes=$(wc -c < "$out")
      maxrss=$(grep -F "Maximum resident set size" "$log" | awk '{print $6}' || true)
      elapsed=$(grep -F "Elapsed (wall clock) time" "$log" | sed 's/.*: //' || true)
      summary=$(grep -F "PFTEmit[$thy]: summary" "$log" | tail -1 || true)
      echo "DIAG_DONE theory=$thy status=$st trace_bytes=$bytes out_bytes=$out_bytes maxrss_kb=${maxrss:-} elapsed=${elapsed:-}"
      [[ -n "$summary" ]] && echo "$summary"
      if [[ $st -ne 0 ]]; then
        echo "DIAG_FAIL theory=$thy status=$st see=$log"
      fi
    done
    echo "DIAG_LOGDIR $LOGDIR"
    ;;
  summarize)
    python3 - "$LOGDIR" <<'PY'
import glob, os, re, sys, csv
logdir = sys.argv[1]
fields = [
  'theory','status','elapsed','maxrss_kb','trace_bytes','out_bytes',
  'heap_size','n_ty','n_tm','n_th',
  'rss_kb','hwm_kb',
  'fi_queries','fi_misses','fi_total_fvs','fi_max_fvs','fi_total_open_bvs','fi_max_open_bvs',
  'tm_memo_hits','tm_memo_misses','tm_memo_sets',
  'th_memo_hits','th_memo_misses','th_memo_sets',
  'ty_memo_hits','ty_memo_misses','ty_memo_sets',
  'pft_fv_queries','pft_fv_misses','pft_fv_total_size','pft_fv_max_size',
  'refl','trans','mk_comb','abs','beta','assume','eq_mp','deduct','inst','inst_type','sym','prove_hyp','new_spec','compute'
]
rows=[]
for f in sorted(glob.glob(os.path.join(logdir,'*.log'))):
    text=open(f,errors='ignore').read()
    thy=os.path.basename(f)[:-4]
    row={k:'' for k in fields}; row['theory']=thy
    m=re.search(r'Exit status: (\d+)', text); row['status']=m.group(1) if m else ''
    m=re.search(r'Elapsed \(wall clock\) time.*: (.*)', text); row['elapsed']=m.group(1).strip() if m else ''
    m=re.search(r'Maximum resident set size \(kbytes\): (\d+)', text); row['maxrss_kb']=m.group(1) if m else ''
    summ=''
    for line in text.splitlines():
        if f'PFTEmit[{thy}]: summary' in line: summ=line
    if summ:
        for k,v in re.findall(r'(\w+)=(-?\d+)', summ):
            if k in row: row[k]=v
        if 'prim_totals=' in summ:
            prim=summ.split('prim_totals=',1)[1]
            for k,v in re.findall(r'(\w+)=(-?\d+)', prim):
                if k in row: row[k]=v
    rows.append(row)
writer=csv.DictWriter(sys.stdout, fieldnames=fields)
writer.writeheader(); writer.writerows(rows)
PY
    ;;
  *)
    echo "Usage: $0 list [N] | run ./emit-candle-merged [N] [LOGDIR] | summarize LOGDIR" >&2
    exit 2
    ;;
esac
