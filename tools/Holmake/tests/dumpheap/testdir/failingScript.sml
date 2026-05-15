open HolKernel Parse boolLib

val _ = new_theory "failing";

(* ALL_TAC leaves the goal unsolved, so TAC_PROOF raises HOL_ERR.
   Under default Holmake (qof) this drives the dump-and-exit path in
   boolLib.store_thm_at; under --noqof it drives the dump-and-continue
   path in holmakebuild.basic_prover.  Either way, a file named
   "failing.bad_thm.dumpedheap" should appear in the testdir. *)
val bad_thm =
    store_thm("bad_thm", ``!x:bool. x = T \/ x = F``, ALL_TAC);

val _ = export_theory();
