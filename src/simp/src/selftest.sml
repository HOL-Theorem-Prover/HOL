open HolKernel Parse boolLib simpLib

(* magic to ensure that interruptions (SIGINTs) are actually seen by the
   linked executable as Interrupt exceptions *)
prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;

val const_term = ``ARB : bool -> bool (ARB : bool -> bool ARB)``
val test_term = ``^const_term /\ x /\ y``

fun infloop_protect startstr endfn f x = let
  val _ =  print (StringCvt.padRight #" " 70 startstr)
  val r = f x
in
  if endfn r then
    (print "OK\n"; (true, r))
  else
    (print "FAILED\n"; (false, r))
end handle Interrupt => (print "FAILED\n"; (false, TRUTH))

(* earlier versions of the simplifier would go into an infinite loop on
   terms of this form. *)
val (test1_flag, result1) =
    infloop_protect
      "AC looping (if this test appears to hang, it has failed)... "
      (K true)
      (QCONV (SIMP_CONV boolSimps.bool_ss
                        [AC CONJ_ASSOC CONJ_COMM]))
      test_term

(* test that AC works with the arguments messed up *)
fun test2P th2 = aconv (rhs (concl result1)) (rhs (concl th2))
val (test2_flag, _) =
    infloop_protect "Permuted AC arguments... "
                    test2P
                    (QCONV (SIMP_CONV boolSimps.bool_ss
                                      [AC CONJ_COMM CONJ_ASSOC]))
                    test_term

(* test bounded simplification *)
fun test3P th = aconv (rhs (concl th)) ``P(f (g (x:'a):'a) : 'a):bool``
val (test3_flag, _) =
    infloop_protect
      "Bounded rewrites (if this test appears to hang, it has failed)... "
      test3P
      (QCONV (SIMP_CONV boolSimps.bool_ss
                        [Once (Q.ASSUME `x:'a = f (y:'a)`),
                         Q.ASSUME `y:'a = g (x:'a)`]))
      ``P (x:'a) : bool``

(* ---------------------------------------------------------------------- *)

val _ = Process.exit (if List.all I [test1_flag, test2_flag, test3_flag] then
                        Process.success
                      else
                        Process.failure);
