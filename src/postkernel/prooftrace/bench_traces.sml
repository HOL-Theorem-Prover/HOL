(* Proof trace benchmarks.
   Run: cd $HOLDIR && bin/hol < src/postkernel/bench_traces.sml

   Requires: a traced build (HOL_TRACE_PROOFS=1 bin/build) exists.
   Measures parse, replay, and chain verification throughput.
   Output is machine-parseable (KEY=VALUE lines prefixed with BENCH:). *)

load "ReplayTrace";

fun its n = Int.toString n
fun timer f =
  let val t0 = Timer.startRealTimer ()
      val result = f ()
      val elapsed = Timer.checkRealTimer t0
  in (result, Time.toMilliseconds elapsed) end

fun bench key value = print ("BENCH: " ^ key ^ "=" ^ value ^ "\n")

val holdir = Globals.HOLDIR;

(* ================================================================
   T6.4: Trace file size stats
   ================================================================ *)

val _ = print "\n=== T6.4: File size stats ===\n";

val traces = ReplayTrace.find_traces (holdir ^ "/src");
val n_traces = length traces;
val _ = bench "n_traces" (its n_traces);

fun file_size path =
  IntInf.toInt (OS.FileSys.fileSize path) handle _ => 0;

val sizes = List.map (fn (_, p) => (p, file_size p)) traces;
val total_bytes = List.foldl (fn ((_,s), acc) => acc + s) 0 sizes;
val _ = bench "total_bytes" (its total_bytes);
val _ = bench "total_mb" (its (total_bytes div (1024 * 1024)));

(* Sort by size descending *)
val sorted = Listsort.sort (fn ((_,a),(_,b)) => Int.compare(b,a)) sizes;
val _ = bench "largest_file" (let val (p,s) = hd sorted
                              in p ^ " (" ^ its s ^ " bytes)" end);
val _ = bench "smallest_file" (let val (p,s) = List.last sorted
                               in p ^ " (" ^ its s ^ " bytes)" end);

val count = length sorted;
fun percentile pct =
  let val idx = Int.min(count - 1, Real.floor(Real.fromInt count * pct))
  in #2 (List.nth(sorted, idx)) end;
val _ = bench "p50_bytes" (its (percentile 0.5));
val _ = bench "p90_bytes" (its (percentile 0.9));
val _ = bench "p99_bytes" (its (percentile 0.99));

(* ================================================================
   T6.5: Parse throughput (decompress + read + tokenize, no replay)
   ================================================================ *)

val _ = print "\n=== T6.5: Parse throughput ===\n";

val total_types = ref 0;
val total_terms = ref 0;
val total_steps = ref 0;
val total_exports = ref 0;

fun parse_one (_, path) =
  let val {n_types, n_terms, n_steps, n_exports} =
        ReplayTrace.parse_trace_stats path
  in total_types := !total_types + n_types;
     total_terms := !total_terms + n_terms;
     total_steps := !total_steps + n_steps;
     total_exports := !total_exports + n_exports
  end;

val ((), parse_ms) = timer (fn () => List.app parse_one traces);
val _ = bench "parse_all_ms" (LargeInt.toString parse_ms);
val _ = bench "total_types" (its (!total_types));
val _ = bench "total_terms" (its (!total_terms));
val _ = bench "total_steps" (its (!total_steps));
val _ = bench "total_exports" (its (!total_exports));
val parse_mbps = if parse_ms > 0
  then Real.fmt (StringCvt.FIX (SOME 1))
         (Real.fromInt total_bytes / (Real.fromLargeInt parse_ms * 1000.0))
  else "inf";
val _ = bench "parse_throughput_mbps" parse_mbps;

(* ================================================================
   T6.6: Replay throughput (full replay with COMPUTE verification)
   ================================================================ *)

val _ = print "\n=== T6.6: Replay throughput ===\n";

val traces_sorted =
  Listsort.sort (fn ((_,a),(_,b)) => String.compare(a,b)) traces;

val n_ok = ref 0;
val n_fail = ref 0;
val n_skip = ref 0;

fun replay_one (thy, path) =
  let
    val loaded = (load (thy ^ "Theory"); true) handle _ => false
  in
    if not loaded then n_skip := !n_skip + 1
    else if ReplayTrace.verify_verbose path
    then n_ok := !n_ok + 1
    else n_fail := !n_fail + 1
  end
  handle _ => n_fail := !n_fail + 1;

val ((), replay_ms) = timer (fn () => List.app replay_one traces_sorted);
val _ = bench "replay_all_ms" (LargeInt.toString replay_ms);
val _ = bench "replay_ok" (its (!n_ok));
val _ = bench "replay_fail" (its (!n_fail));
val _ = bench "replay_skip" (its (!n_skip));
val replay_avg =
  if n_traces > 0
  then LargeInt.toString (replay_ms div LargeInt.fromInt n_traces)
  else "0";
val _ = bench "replay_avg_ms" replay_avg;

(* ================================================================
   T6.7: Chain verification (end-to-end, deepest theory)
   ================================================================ *)

(* Chain verification removed — use merge tool + from-scratch replay *)

(* ================================================================
   Summary
   ================================================================ *)

val _ = print "\n========================================\n";
val _ = print "PROOF TRACE BENCHMARK SUMMARY\n";
val _ = print ("Traces:           " ^ its n_traces ^ "\n");
val _ = print ("Total size:       " ^ its (total_bytes div (1024*1024)) ^ " MB\n");
val _ = print ("Types/terms/steps:" ^
               " " ^ its (!total_types) ^
               "/" ^ its (!total_terms) ^
               "/" ^ its (!total_steps) ^ "\n");
val _ = print ("Exports:          " ^ its (!total_exports) ^ "\n");
val _ = print ("Parse (all):      " ^ LargeInt.toString parse_ms ^ " ms\n");
val _ = print ("Parse throughput:  " ^ parse_mbps ^ " MB/s\n");
val _ = print ("Replay (all):     " ^ LargeInt.toString replay_ms ^ " ms (" ^
               its (!n_ok) ^ "/" ^ its (!n_fail) ^ "/" ^ its (!n_skip) ^
               " ok/fail/skip)\n");
val _ = print ("Chain (" ^ chain_thy ^ "): " ^
               LargeInt.toString chain_ms ^ " ms (" ^
               its (#ok chain_result) ^ " ok, " ^
               its (#fail chain_result) ^ " fail)\n");
val _ = print "(Export phase breakdown: run bench_build.sh)\n";
val _ = print "========================================\n";

val _ = OS.Process.exit (if !n_fail = 0 andalso #fail chain_result = 0
                         then OS.Process.success
                         else OS.Process.failure);
