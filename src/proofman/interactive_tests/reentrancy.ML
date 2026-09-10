(* A tactic run by expand may itself drive the proof manager: TotalDefn
   hands a failed termination goal to it, and Defn.tprove used to prove
   through it.  expand must not hold the proofs slot's lock while the
   tactic runs.  A regression wedges the session with interrupts masked,
   so a watchdog thread turns it into a failure instead. *)

val _ = List.app load ["testutils", "Standard_Thread", "Synchronized"];

open HolKernel boolLib testutils proofManagerLib;

val _ = chatting := false;

val finished = Synchronized.var "reentrancy.finished" false;
val _ =
    Standard_Thread.fork
      {name = "reentrancy.watchdog", stack_limit = NONE, interrupts = false}
      (fn () =>
          case Synchronized.timed_access finished
                 (fn _ => SOME (Time.+ (Time.now (), Time.fromSeconds 120)))
                 (fn true => SOME ((), true) | false => NONE) of
            SOME () => ()
          | NONE => die "proof manager deadlocked");

val passed = ref 0;
fun ok () = (passed := !passed + 1; OK ());

val T_goal : goal = ([], T);
val private_goal : goal = ([], mk_var ("private_goal", bool));

fun no_proofs () = (p (); false) handle HOL_ERR _ => true;
fun top_is (g : goal) = aconv (snd (top_goal ())) (snd g) handle _ => false;

(* the proof-manager traffic Defn.tprove used to generate *)
fun nested_proof_tac (g : goal) =
    let val _ = set_goal T_goal
        val _ = e (ACCEPT_TAC TRUTH)
        val th = top_thm ()
        val _ = drop ()
    in ACCEPT_TAC th g end;

fun test_entry (name, expand) =
    (tprint (name ^ ": tactic that uses the proof manager itself");
     set_goal T_goal;
     expand nested_proof_tac;
     if aconv (concl (top_thm ())) T andalso (drop (); no_proofs ()) then ok ()
     else die "wrong proof state");

val _ = List.app test_entry
          [("e", ignore o e), ("expandf", ignore o expandf),
           ("eall", ignore o eall),
           ("expand_listf", ignore o expand_listf o ALLGOALS)];

val _ = tprint "e: goal pushed by a failing tactic stays on the stack";
val _ = set_goal T_goal;
fun push_and_fail (g : goal) =
    (set_goal private_goal; raise mk_HOL_ERR "reentrancy" "push_and_fail" "");
val _ = (e push_and_fail; die "e succeeded") handle HOL_ERR _ => ();
val _ = if top_is private_goal andalso (drop (); top_is T_goal)
           andalso (drop (); no_proofs ())
        then ok () else die "wrong proof state";

val _ = tprint "e: goal pushed by a successful tactic is discarded";
val _ = set_goal T_goal;
fun push_and_succeed (g : goal) = (set_goal private_goal; ACCEPT_TAC TRUTH g);
val _ = e push_and_succeed;
val _ = if aconv (concl (top_thm ())) T andalso (drop (); no_proofs ())
        then ok () else die "wrong proof state";

val _ = Synchronized.change finished (fn _ => true);
val _ = if !passed = 6 then OS.Process.exit OS.Process.success
        else die ("only " ^ Int.toString (!passed) ^ " of 6 tests ran");
