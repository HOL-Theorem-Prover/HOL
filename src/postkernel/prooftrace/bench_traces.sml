(* Proof trace benchmarks.
   Run: cd $HOLDIR && bin/hol --min < src/postkernel/prooftrace/bench_traces.sml

   Requires: a traced build (HOL_TRACE_PROOFS=1 bin/build) and a merged trace.
   Measures replay throughput.
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

(* Find all per-theory traces *)
val traces = ReplayTrace.find_traces (holdir ^ "/src");
val n_traces = length traces;
val _ = bench "n_traces" (its n_traces);

val _ = print ("\n=== Replay benchmarks (" ^ its n_traces ^ " traces) ===\n\n");

(* Replay each trace and measure time *)
val total_ms = ref (0 : LargeInt.int);
val n_ok = ref 0;
val n_fail = ref 0;

fun replay_one (thy, path) =
  let
    val (exports, ms) = timer (fn () => ReplayTrace.replay_file path)
    val oracle_exports = List.filter (fn (_, th) =>
      not (null (#1 (Tag.dest_tag (Thm.tag th))))) exports
  in
    total_ms := !total_ms + ms;
    if null oracle_exports then n_ok := !n_ok + 1
    else n_fail := !n_fail + 1;
    bench ("replay_" ^ thy ^ "_ms") (LargeInt.toString ms);
    bench ("replay_" ^ thy ^ "_exports") (its (length exports))
  end
  handle e =>
    (n_fail := !n_fail + 1;
     print ("ERROR on " ^ thy ^ ": " ^ General.exnMessage e ^ "\n"));

val _ = List.app replay_one traces;

val _ = print "\n========================================\n";
val _ = bench "total_replay_ms" (LargeInt.toString (!total_ms));
val _ = bench "replay_ok" (its (!n_ok));
val _ = bench "replay_fail" (its (!n_fail));
val _ = print "========================================\n";
