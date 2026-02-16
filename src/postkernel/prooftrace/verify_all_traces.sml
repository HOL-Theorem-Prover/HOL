(* Batch verification of all .pftrace files.
   Run: cd $HOLDIR && bin/hol < src/postkernel/verify_all_traces.sml *)

load "ReplayTrace";
load "cv_computeLib";

(* Enable COMPUTE step verification via cv_compute *)
ReplayTrace.compute_verifier := SOME (cv_computeLib.cv_compute []);

val holdir = Globals.HOLDIR;

(* Find all .pftrace files *)
val traces = ReplayTrace.find_traces (holdir ^ "/src");

val _ = print ("\n=== Verifying " ^ Int.toString (length traces) ^
               " proof traces (COMPUTE verification enabled) ===\n\n");

(* Sort by filename for reproducible output *)
val traces = Listsort.sort (fn ((_,a),(_,b)) => String.compare(a,b)) traces;

val n_ok = ref 0;
val n_fail = ref 0;
val n_skip = ref 0;
val failures = ref ([] : string list);
val skipped = ref ([] : string list);

fun verify_one (thy, path) =
  let
    (* Try to load the theory first *)
    val loaded = (load (thy ^ "Theory"); true)
                 handle _ => false
  in
    if not loaded then
      (print ("SKIP: " ^ thy ^ " (theory not loadable)\n");
       n_skip := !n_skip + 1;
       skipped := thy :: !skipped)
    else if ReplayTrace.verify_verbose path
    then n_ok := !n_ok + 1
    else (n_fail := !n_fail + 1;
          failures := thy :: !failures)
  end
  handle e =>
    (print ("ERROR on " ^ thy ^ ": " ^ exn_to_string e ^ "\n");
     n_fail := !n_fail + 1;
     failures := thy :: !failures);

val _ = List.app verify_one traces;

val _ = print ("\n========================================\n");
val _ = print ("TOTAL: " ^ Int.toString (!n_ok) ^ " OK, " ^
               Int.toString (!n_fail) ^ " FAILED, " ^
               Int.toString (!n_skip) ^ " SKIPPED out of " ^
               Int.toString (length traces) ^ "\n");
val _ = if null (!failures) then ()
        else (print "Failed theories:\n";
              List.app (fn f => print ("  " ^ f ^ "\n")) (rev (!failures)));
val _ = if null (!skipped) then ()
        else (print "Skipped (not loadable):\n";
              List.app (fn f => print ("  " ^ f ^ "\n")) (rev (!skipped)));
val _ = print "========================================\n";

val _ = OS.Process.exit (if !n_fail = 0
                         then OS.Process.success
                         else OS.Process.failure);
