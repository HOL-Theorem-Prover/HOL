open HolKernel Parse boolLib simpLib

(* magic to ensure that interruptions (SIGINTs) are actually seen by the
   linked executable as Interrupt exceptions *)
prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;

val const_term = ``ARB : bool -> bool (ARB : bool -> bool ARB)``
val test_term = ``^const_term /\ x /\ y``

fun infloop_protect startstr endstr f x = let
  val _ =  print startstr
  val result = f x
      handle Interrupt => (print "\n"; Process.exit Process.failure);
in
  print endstr ;
  result
end

(* earlier versions of the simplifier would go into an infinite loop on
   terms of this form. *)
val result1 =
    infloop_protect "1. If this test appears to hang; it has FAILED... "
                    "[Completed]\n"
                    (QCONV (SIMP_CONV boolSimps.bool_ss
                                      [AC CONJ_ASSOC CONJ_COMM]))
                    test_term
val test1_flag = true
val _ = print "Test 1 OK\n"

(* test that AC works with the arguments messed up *)
val result2 =
    infloop_protect "2. Testing messed up AC arguments... "
                    "done\n"
                    (QCONV (SIMP_CONV boolSimps.bool_ss
                                      [AC CONJ_COMM CONJ_ASSOC]))
                    test_term

val test2_flag =
    Term.compare (rhs (concl result1), rhs (concl result2)) = EQUAL
val _ = if test2_flag then print "Test 2 OK\n"
        else print "Test 2 FAILED\n"

(* ---------------------------------------------------------------------- *)

val _ = Process.exit (if List.all I [test1_flag, test2_flag] then
                        Process.success
                      else
                        Process.failure);
