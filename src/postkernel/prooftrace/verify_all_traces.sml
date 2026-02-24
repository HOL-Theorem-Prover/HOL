(* Batch replay of all .pft files.
   Run: cd $HOLDIR && bin/hol --min < src/postkernel/prooftrace/verify_all_traces.sml *)

load "ReplayTrace";

val holdir = Globals.HOLDIR;
val traces = ReplayTrace.find_traces (holdir ^ "/src");

val _ = print ("\n=== Replaying " ^ Int.toString (length traces) ^
               " proof traces ===\n\n");

val n_ok = ref 0;
val n_fail = ref 0;

fun replay_one (thy, path) =
  let
    val _ = print (thy ^ " ... ")
    val exports = ReplayTrace.replay_file path
    val n = length exports
    val oracle_exports = List.filter (fn (_, th) =>
      not (null (#1 (Tag.dest_tag (Thm.tag th))))) exports
  in
    if null oracle_exports then
      (print ("OK (" ^ Int.toString n ^ " exports)\n");
       n_ok := !n_ok + 1)
    else
      (print ("FAIL: " ^ Int.toString (length oracle_exports) ^
              "/" ^ Int.toString n ^ " exports have oracle tags\n");
       n_fail := !n_fail + 1)
  end
  handle e =>
    (print ("ERROR: " ^ General.exnMessage e ^ "\n");
     n_fail := !n_fail + 1);

val _ = List.app replay_one traces;

val _ = print ("\n========================================\n");
val _ = print ("TOTAL: " ^ Int.toString (!n_ok) ^ " OK, " ^
               Int.toString (!n_fail) ^ " FAILED\n");
val _ = print "========================================\n";
