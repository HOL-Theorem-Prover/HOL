open HolKernel Parse boolLib simpLib

val _ = print "If this test appears to hang; it has FAILED... "
val const_term = ``ARB : bool -> bool (ARB : bool -> bool ARB)``
val test_term = ``^const_term /\ x /\ y``

(* earlier versions of the simplifier would go into an infinite loop on
   terms of this form. *)
val result = QCONV (SIMP_CONV boolSimps.bool_ss [AC CONJ_ASSOC CONJ_COMM])
                   test_term;
val _ = print "[Completed]\n";

val test1_flag = Term.aconv (rhs (concl result)) test_term


val _ = Process.exit Process.success
                      (* (if List.all I [test1_flag] then
                            Process.success
                          else
                            Process.failure); *)
