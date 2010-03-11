open HolKernel Parse boolLib simpLib

val _ = Portable.catch_SIGINT()

fun infloop_protect (startstr : string) (endfn : 'a -> bool)
    (f : 'b -> 'a) (x : 'b) =
    let
      val _ =  print (StringCvt.padRight #" " 70 startstr)
      val r = f x
    in
      if endfn r then
        (print "OK\n"; (true, SOME r))
      else
        (print "FAILED\n"; (false, SOME r))
    end handle Interrupt => (print "FAILED\n"; (false, NONE))
             | e => (print "EXN\n"; Raise e)

(* earlier versions of the simplifier would go into an infinite loop on
   terms of this form. *)
val const_term = ``(ARB : bool -> bool) ((ARB : bool -> bool) ARB)``
val test_term = ``^const_term /\ x /\ y``

val (test1_flag, result1) =
    infloop_protect
      "AC looping (if this test appears to hang, it has failed)... "
      (K true)
      (QCONV (SIMP_CONV boolSimps.bool_ss
                        [AC CONJ_ASSOC CONJ_COMM]))
      test_term

(* test that AC works with the arguments messed up *)
fun test2P th2 = aconv (rhs (concl (valOf result1))) (rhs (concl th2))
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

(* test abbreviations in tactics *)
fun test4P (sgs, vfn) =
    length sgs = 1 andalso
    (let val (asms, gl) = hd sgs
     in
       aconv gl ``Q (f (x:'a) : 'b) : bool`` andalso
       length asms = 1 andalso
       aconv (hd asms) ``P (f (x:'a) : 'b) : bool``
     end)

val (test4_flag, _) =
    infloop_protect
      "Abbreviations + ASM_SIMP_TAC... "
      test4P
      (ASM_SIMP_TAC boolSimps.bool_ss [markerSyntax.Abbr`y`])
      ([``Abbrev (y:'b = f (x : 'a))``, ``P (y:'b) : bool``],
       ``Q (y:'b) : bool``)

(* test that bounded rewrites get applied to both branches, and also that
   the bound on the rewrite allows it to apply at all (normally it wouldn't)
*)
val goal5 = ``(x:'a = y) <=> (y = x)``
val test5P =
    infloop_protect
        "Bounded rewrites branch, and bypass permutative loop check"
        (fn (sgs, vf) => null sgs andalso let
                           val th = vf []
                         in
                           aconv (concl th) goal5 andalso null (hyp th)
                         end)
        (fn g => (EQ_TAC THEN STRIP_TAC THEN
                  SIMP_TAC boolSimps.bool_ss [Once EQ_SYM_EQ] THEN
                  POP_ASSUM ACCEPT_TAC) g)
        ([], goal5)

val test5_flag = #1 test5P

(* test that being a bounded rewrite overrides detection of loops in
   mk_rewrites code *)
val (test6_flag, _) = let
  open boolSimps
  val rwt_th = ASSUME ``!x:'a. (f:'a -> 'b) x = if P x then z
                                     else let x = g x in f x``
  val Pa_th = ASSUME ``P (a:'a) : bool``
  fun doit t = (QCONV (SIMP_CONV bool_ss [Pa_th, Once rwt_th]) t,
                QCONV (SIMP_CONV bool_ss [Pa_th, rwt_th]) t)
  fun check (th1, th2) =
      aconv (rhs (concl th1)) ``z:'b`` andalso length (hyp th1) = 2 andalso
      aconv (rhs (concl th2)) ``f (a:'a):'b``
in
  infloop_protect
      "Bounded rewrites override mk_rewrites loop check"
      check
      doit
      ``f (a:'a) : 'b``
end

(* test that a bounded rewrite on a variable gets a chance to fire at all *)
val (test7_flag, _) = let
  open pureSimps
  val rwt_th = ASSUME ``!x:'a. x:'a = f x``
  val t = ``x:'a = z``
  fun doit t = QCONV (SIMP_CONV pure_ss [Once rwt_th]) t
  fun check th = aconv (rhs (concl th)) ``f (x:'a):'a = z``
in
  infloop_protect
      "Bounded rewrites on variables don't get decremented prematurely"
      check
      doit
      t
end

(* test that a bound on a rewrite applies to all derived rewrite theorems *)
val (test8_flag, _) = let
  open boolSimps
  val rwt_th = ASSUME ``(p:bool = x) /\ (q:bool = x)``
  val t = ``p /\ q``
  fun doit t = QCONV (SIMP_CONV bool_ss [Once rwt_th]) t
  fun check th = not (aconv (rhs (concl th)) ``x:bool``)
in
  infloop_protect
      "Bound on rewrites applies to all derived theorems jointly."
      check
      doit
      t
end

(* ---------------------------------------------------------------------- *)

val _ = Process.exit
          (if List.all I [test1_flag, test2_flag, test3_flag, test4_flag,
                          test5_flag, test6_flag, test7_flag, test8_flag]
           then
             Process.success
           else
             Process.failure);
