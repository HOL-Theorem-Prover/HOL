#!/bin/bash
# Benchmark build time with and without proof tracing.
# Run from $HOLDIR: bash src/postkernel/prooftrace/bench_build.sh
#
# Performs two clean builds and reports wall-clock times.
# Extracts per-phase export timings from per-theory log files.
# Then runs bench_traces.sml for replay/parse benchmarks.
#
# Output: machine-parseable BENCH: lines + summary.

set -euo pipefail
cd "$(dirname "$0")/../.."  # cd to HOLDIR

echo "=== Benchmark: build without tracing ==="
bin/build cleanAll >/dev/null 2>&1
T0=$(date +%s%N)
bin/build >/dev/null 2>&1
T1=$(date +%s%N)
NOTRACE_MS=$(( (T1 - T0) / 1000000 ))
echo "BENCH: build_notrace_ms=$NOTRACE_MS"

echo ""
echo "=== Benchmark: build with tracing + phase timing ==="
bin/build cleanAll >/dev/null 2>&1
T0=$(date +%s%N)
HOL_TRACE_PROOFS=1 HOL_TRACE_BENCHMARKS=1 bin/build >/dev/null 2>&1
T1=$(date +%s%N)
TRACE_MS=$(( (T1 - T0) / 1000000 ))
echo "BENCH: build_trace_ms=$TRACE_MS"

OVERHEAD_MS=$((TRACE_MS - NOTRACE_MS))
if [ "$NOTRACE_MS" -gt 0 ]; then
    OVERHEAD_PCT=$((OVERHEAD_MS * 100 / NOTRACE_MS))
else
    OVERHEAD_PCT=0
fi
echo "BENCH: build_overhead_ms=$OVERHEAD_MS"
echo "BENCH: build_overhead_pct=$OVERHEAD_PCT"

# Aggregate TRACE_BENCH lines from per-theory log files
echo ""
echo "=== Export phase breakdown (aggregated from theory logs) ==="
find src -path '*/.hol/logs/*Theory' -exec grep '^TRACE_BENCH:' {} \; \
  | awk '{
    n++
    for (i=3; i<=NF; i++) {
        split($i, kv, "=")
        sums[kv[1]] += kv[2]
        if (kv[1] == "total" && kv[2]+0 > max) { max = kv[2]+0; maxthy = $2 }
    }
}
END {
    if (n > 0) {
        printf "BENCH: export_count=%d\n", n
        printf "BENCH: export_total_ms=%d\n", sums["total"]
        printf "BENCH: export_reach_ms=%d\n", sums["reach"]
        printf "BENCH: export_raw_ms=%d\n", sums["raw"]
        printf "BENCH: export_dedup_ms=%d\n", sums["dedup"]
        printf "BENCH: export_prune_ms=%d\n", sums["prune"]
        printf "BENCH: export_opt_ms=%d\n", sums["opt"]
        printf "BENCH: export_max_theory=%s (%dms)\n", maxthy, max
        stream = '$OVERHEAD_MS' - sums["total"]
        printf "BENCH: stream_overhead_ms=%d\n", stream
    }
}'

echo ""
echo "=== Replay + parse benchmarks ==="
bin/hol < src/postkernel/prooftrace/bench_traces.sml 2>&1 | grep -E '^BENCH:|^PROOF|^  '

echo ""
echo "========================================"
echo "BUILD OVERHEAD SUMMARY"
echo "  Without tracing:  ${NOTRACE_MS} ms"
echo "  With tracing:     ${TRACE_MS} ms"
echo "  Total overhead:   ${OVERHEAD_MS} ms (${OVERHEAD_PCT}%)"
echo ""
echo "  Export phase breakdown:"
find src -path '*/.hol/logs/*Theory' -exec grep '^TRACE_BENCH:' {} \; \
  | awk '{
    n++
    for (i=3; i<=NF; i++) {
        split($i, kv, "=")
        sums[kv[1]] += kv[2]
    }
}
END {
    if (n > 0) {
        printf "    reachability:   %d ms\n", sums["reach"]
        printf "    raw write:      %d ms\n", sums["raw"]
        printf "    dedup:          %d ms\n", sums["dedup"]
        printf "    prune:          %d ms\n", sums["prune"]
        printf "    opt write:      %d ms\n", sums["opt"]
        printf "    export total:   %d ms\n", sums["total"]
        stream = '$OVERHEAD_MS' - sums["total"]
        printf "    stream record:  ~%d ms (overhead - export)\n", stream
    }
}'
echo "========================================"
