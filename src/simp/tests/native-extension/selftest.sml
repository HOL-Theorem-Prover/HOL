structure selftest =
struct

open NativePrelude

open HolKernel Parse boolLib simpLib splitLib
open testutils boolSimps

val _ = new_theory "scratch"

val failcount = ref 0
val _ = diemode := Remember failcount

val _ = Portable.catch_SIGINT()

(* earlier versions of the simplifier would go into an infinite loop on
   terms of this form. *)
val const_term = ``(ARB : bool -> bool) ((ARB : bool -> bool) ARB)``
val test_term = ``^const_term /\ x /\ y``

val _ = tprint "AC looping (if test appears to hang, it has failed)"
val _ = let
  fun kont result1 =
      let
        fun test2P th2 =
            aconv (rhs (concl (Exn.release result1))) (rhs (concl th2))
      in
        (tprint "Permuted AC arguments";
         require (check_result test2P)
                 (QCONV (SIMP_CONV bool_ss [AC CONJ_COMM CONJ_ASSOC]))
                 test_term)
      end
in
  require_msgk (check_result (K true)) (fn _ => HOLPP.add_string "")
               (QCONV (SIMP_CONV bool_ss [AC CONJ_ASSOC CONJ_COMM]))
               kont
               test_term
end

fun infloop_protect msg check f x =
    (tprint msg; require (check_result check) f x)

(* test bounded simplification *)
fun test3P th = aconv (rhs (concl th)) ``P(f (g (x:'a):'a) : 'a):bool``
val _ =
    infloop_protect
      "Bounded rewrites (if test appears to hang, it has failed)"
      test3P
      (QCONV (SIMP_CONV bool_ss
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

val _ =
    infloop_protect
      "Abbreviations + ASM_SIMP_TAC"
      test4P
      (runtac (VALID (ASM_SIMP_TAC bool_ss [markerSyntax.Abbr`y`])))
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
        (runtac (EQ_TAC THEN STRIP_TAC THEN
                 SIMP_TAC bool_ss [Once EQ_SYM_EQ] THEN
                 POP_ASSUM ACCEPT_TAC))
        ([], goal5)

(* test that being a bounded rewrite overrides detection of loops in
   mk_rewrites code *)
val _ = let
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

(* test that loop detection doesn't trigger on bound variables *)
val _ =
    convtest ("Loop detection doesn't trigger on bound variable",
              SIMP_CONV boolSimps.bool_ss
                        [ASSUME “a:'a = (\a:'a b:'b. a) x y”],
              “f(a:'a) = z:'c”,
              “f(x:'a) = z:'c”);

(* A congruence rule whose conclusion applies a higher-order variable to
   the bound variable of the subterm that variable stands for has the
   variable instantiated with an abstraction, and every such application
   is then a beta redex.  A rebuilt term is not traversed again, so an
   unreduced redex survives into the result and no rule stated in the
   ordinary spelling can read it. *)
val _ = let
  val bounded_exists_cong = prove(
    ``(!x:'a. P x = Q x) ==> (!x:'a. Q x ==> (f x = g x)) ==>
      ((?x:'a. P x /\ f x) = (?x:'a. Q x /\ g x))``,
    REPEAT DISCH_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    ASM_REWRITE_TAC [] THEN ASM_CASES_TAC ``Q (x:'a) : bool`` THEN
    RES_TAC THEN ASM_REWRITE_TAC [])
  val cong_ss =
    name_ss "BOUNDEDEXISTS" (threaded_cong_ss [bounded_exists_cong])
  val ordinary_cong_ss =
    SSFRAG {name = SOME "ORDINARYBOUNDEDEXISTS",
            congs = [bounded_exists_cong], convs = [], rewrs = [],
            ac = [], filter = NONE, dprocs = []}
  val tm = ``?x:'a. (x = x) /\ C x``
  val ordinary_result = ``?x:'a. (\x:'a. T) x /\ C x``
  val mixed_ss = bool_ss ++ merge_ss
    [ordinary_cong_ss, threaded_cong_ss [boolTheory.COND_CONG]]
  val merged_ss = bool_ss ++ merge_ss [empty_ssfrag, cong_ss]
  val replayed_ss = remove_ssfrags ["CONG_REPLAY_DECOY"]
    (merged_ss ++ name_ss "CONG_REPLAY_DECOY" empty_ssfrag)
  val _ = convtest
    ("ordinary applied-result congruence keeps the ordinary beta redex",
     SIMP_CONV (bool_ss ++ ordinary_cong_ss) [], tm, ordinary_result)
  val _ = convtest
    ("Cong marker keeps ordinary applied-result handling",
     SIMP_CONV bool_ss [Cong bounded_exists_cong], tm, ordinary_result)
  val _ = convtest
    ("threaded rules do not opt ordinary rules in",
     SIMP_CONV mixed_ss [], tm, ordinary_result)
  val _ = convtest
    ("SF carries threaded congruences",
     SIMP_CONV bool_ss [SF cong_ss], tm, ``?x:'a. T /\ C x``)
  val _ = convtest
    ("merged threaded congruence keeps beta reduction",
     SIMP_CONV merged_ss [], tm, ``?x:'a. T /\ C x``)
  val _ = convtest
    ("history replay keeps threaded congruences",
     SIMP_CONV replayed_ss [], tm, ``?x:'a. T /\ C x``)
in
  convtest ("congruence rebuilds a beta reduced term",
            SIMP_CONV (bool_ss ++ cong_ss) [], tm,
            ``?x:'a. T /\ C x``)
end

(* The term the traversal asked about is the equation's left-hand side.
   It can hold redexes of its own -- here one whose abstraction is the
   very form the first antecedent's result is generalised into -- and
   reducing those answers about a term nobody asked about. *)
val _ = let
  val bounded_exists_cong = prove(
    ``(!x:'a. P x = Q x) ==> (!x:'a. Q x ==> (f x = g x)) ==>
      ((?x:'a. P x /\ f x) = (?x:'a. Q x /\ g x))``,
    REPEAT DISCH_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    ASM_REWRITE_TAC [] THEN ASM_CASES_TAC ``Q (x:'a) : bool`` THEN
    RES_TAC THEN ASM_REWRITE_TAC [])
  val cong_ss =
    name_ss "BOUNDEDEXISTS" (threaded_cong_ss [bounded_exists_cong])
  val redex_term = ``?x:'a. (x = x) /\ D ((\y:'a. T) x)``
  val _ = tprint "congruence answers about the term it was given"
in
  case Lib.total (SIMP_CONV (bool_ss ++ cong_ss) []) redex_term of
      NONE => die "simplification failed"
    | SOME th =>
        if aconv (lhs (concl th)) redex_term then OK ()
        else die ("left-hand side became " ^ term_to_string (lhs (concl th)))
end

(* An antecedent stating an intermediate result -- one a later
   antecedent consumes rather than the conclusion naming it -- is a
   sub-congruence for the traversal to supply, not a side condition for
   the solver.  Here the rebuilt conjunction is handed back to the
   traversal so that the node the rule matched is still one the rewrites
   and any further congruence reach. *)
val _ = let
  val threaded_cong = prove(
    ``(!x:'a. P x = Q x) ==> (!x:'a. Q x ==> (f x = g x)) ==>
      (!x:'a. (Q x /\ g x) = h x) ==>
      ((?x:'a. P x /\ f x) = (?x:'a. h x))``,
    DISCH_TAC THEN DISCH_TAC THEN
    DISCH_THEN (fn rebuilt => REWRITE_TAC [GSYM rebuilt]) THEN
    AP_TERM_TAC THEN ABS_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC ``Q (x:'a) : bool`` THEN RES_TAC THEN ASM_REWRITE_TAC [])
  val cong_ss = name_ss "THREADED" (threaded_cong_ss [threaded_cong])
  val ordinary_cong_ss =
    SSFRAG {name = SOME "ORDINARYTHREADED", congs = [threaded_cong],
            convs = [], rewrs = [], ac = [], filter = NONE, dprocs = []}
  val rewrs = [ASSUME ``!y:'a. bnd y ==> (bdy y <=> bdy' y)``]
  val tm = ``?x:'a. bnd x /\ bdy x``
  val _ = convtest
    ("ordinary intermediate-result congruence keeps the ordinary result",
     QCONV (SIMP_CONV (bool_ss ++ ordinary_cong_ss) rewrs), tm, tm)
  val _ = convtest
    ("Cong marker keeps ordinary intermediate-result handling",
     QCONV (SIMP_CONV bool_ss (Cong threaded_cong :: rewrs)), tm, tm)
in
  convtest ("congruence threads an intermediate result",
            SIMP_CONV (bool_ss ++ cong_ss) rewrs, tm,
            ``?x:'a. bnd x /\ bdy' x``)
end

(* test that a bounded rewrite on a variable gets a chance to fire at all *)
val _ = let
  open pureSimps
  val rwt_th = ASSUME ``!x:'a. x:'a = f x``
  val t = ``x:'a = z``
  fun doit t = QCONV (SIMP_CONV pure_ss [Once rwt_th]) t
  fun check th = aconv (rhs (concl th)) ``f (x:'a):'a = z``
in
  infloop_protect
      "Bounded rwts on variables don't get decremented prematurely"
      check
      doit
      t
end

(* test that a bound on a rewrite applies to all derived rewrite theorems *)
val _ = let
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

(*
(* test improved loop detection *)
val _ = let
  val rwt_th = ASSUME “!x:'a. FN x = if P x then T else FN (g x)”
in
  shouldfail {checkexn = (fn UNCHANGED => true | _ => false),
              printarg = K "Test internal instance loop detection",
              printresult = thm_to_string,
              testfn = SIMP_CONV bool_ss [rwt_th]}
             “FN (n:'a) : bool”
end;
*)

(* test that congruence rule for conditional expressions is working OK *)
val _ = let
  open boolSimps
  val t = ``if a then f a:'a else g a``
  val result = ``if a then f T:'a else g F``
  fun doit t = QCONV (SIMP_CONV bool_ss []) t
  fun check th = aconv (rhs (concl th)) result
in
  infloop_protect "Congruence for conditional expressions" check doit t
end

val _ = let
  open OrdinarySimp OrdinaryBool
  val t = ``I (f:'b -> 'c) o I (g:'a -> 'b)``
  val result = ``(f:'b -> 'c) o I (g:'a -> 'b)``
  val doit = QCONV (SIMP_CONV (bool_ss ++ combinSimps.COMBIN_ss)
                              [SimpL ``$o``])
  fun check th = aconv (rhs (concl th)) result
in
  infloop_protect "SimpL on operator returning non-boolean" check doit t
end

val _ = shouldfail {testfn = (fn () => remove_ssfrags ["FOOBAR"] bool_ss),
                    printresult = PP.pp_to_string 65 simpLib.pp_simpset,
                    printarg = fn () => "remove_ssfrags throws UNCHANGED",
                    checkexn = fn Conv.UNCHANGED => true | _ => false} ()

val _ = let
  open OrdinarySimp OrdinaryBool
  val t = ``(!n:'a. P n n) ==> ?m. P c m``
  val result = ``T``
  val doit = QCONV (SIMP_CONV (bool_ss ++ SatisfySimps.SATISFY_ss) [])
  fun check th = aconv (rhs (concl th)) result
in
  infloop_protect "Satisfy" check doit t
end

val _ = let
  val asm = ``Abbrev(f = (\x. x /\ y))``
  val g = ([asm], ``p /\ y``)
  val doit = runtac (ASM_SIMP_TAC bool_ss [])
  fun geq (asl1, g1) (asl2, g2) =
      aconv g1 g2 andalso
      case (asl1, asl2) of
           ([a1], [a2]) => aconv a1 asm andalso aconv a2 asm
         | _ => false
  fun check (sgs, vfn) = let
    val sgs_ok =
      case sgs of
          [goal] => geq goal ([asm], ``(f:bool -> bool) p``)
        | _ => false
  in
    sgs_ok andalso geq (dest_thm (vfn [mk_thm (hd sgs)])) g
  end
in
  infloop_protect "Abbrev-simplification with abstraction" check doit g
end

(* rewrites on F and T *)
val TF = mk_eq(T,F)
val FT = mk_eq(F,T)

val _ = let
  val t = TF
  val doit = QCONV (SIMP_CONV bool_ss [ASSUME TF, ASSUME FT])
  fun check th = th |> concl |> rhs |> aconv F
in
  infloop_protect "assume T=F and F=T (if hangs, it's failed)" check doit t
end


(* conjunction congruence *)
val _ = let
  val t = list_mk_conj [TF,FT,TF]
  val doit = QCONV (SIMP_CONV (bool_ss ++ CONJ_ss) [])
  fun check th = th |> concl |> rhs |> aconv F
in
  infloop_protect
    "CONJ_ss with T=F and F=T assumptions (if hangs, it's failed)"
    check doit t
end

(* ---------------------------------------------------------------------- *)

val _ = let
  val _ = tprint "Cond_rewr.mk_cond_rewrs on ``hyp ==> (T = e)``"
in
  case Lib.total Cond_rewr.mk_cond_rewrs
                 (ASSUME ``P x ==> (T = Q y)``, BoundedRewrites.UNBOUNDED)
   of
      NONE => die "FAILED!"
    | SOME _ => OK()
end

local
  fun die_r l =
    die ("\n  FAILED!  Incorrectly generated rewrites\n  " ^
         String.concatWith "\n  " (map (thm_to_string o #1) l))
fun testb (s, thm, c) =
  let
    val _ = tprint ("Cond_rewr.mk_cond_rewrs on "^s)
  in
    case Lib.total Cond_rewr.mk_cond_rewrs(thm, BoundedRewrites.UNBOUNDED)
     of
        NONE => die "EXN-FAILED!"
      | SOME l => if length l = c then OK() else die_r l
  end
val lem1 = prove(“a <> b ==> (a = ~b)”,
                 ASM_CASES_TAC “a:bool” THEN ASM_REWRITE_TAC[])
val marker = GSYM markerTheory.Abbrev_def
in
val _ = app testb [
  ("“hyp ==> b”", ASSUME “(!b x y. (P x y = b) ==> b)”, 0),
  ("“hyp ==> ~b”", ASSUME “(!b x y. (p x y = b) ==> ~b)”, 0),
  ("“hyp ==> b=e”", ASSUME “(!b:bool x y. (p x y = b) ==> (b = e))”, 2),
  ("“a <> b ==> (a = ~b)", lem1, 2),
  ("x = Abbrev x", marker, 2)
]

val _ = tprint "Cond_rewr.mk_cond_rewrs on bounded x <=> Abbrev x"
val _ = let
  val b = BoundedRewrites.BOUNDED (ref 1)
in
  case Lib.total Cond_rewr.mk_cond_rewrs (marker, b) of
      NONE => die "EXN-FAILED!"
    | SOME (rs as [(th',b')]) =>
        if concl th' ~~ (marker |> concl |> strip_forall |> #2) then OK()
        else die_r rs
    | SOME rs => die_r rs
end
end (* local fun testb ... *);

val _ = let
  open simpLib boolSimps
  fun del ss s = ss -* ("bool_case_thm" :: s)
  val booleta_ss = bool_ss ++ ETA_ss
  val T_t = “if T then (p:'b) else q”
  val F_t = “if F then (p:'b) else q”
  val beta_t = “(\x:'b. f T x : bool) z”
  val eta_t = “f (\x:'a. g (z:'b) x:'c) : 'd”
  val unwind_t = “?x:'a. p x /\ (x = y) /\ q x y”
  val unwind_beta_t = “?x:'a. p x /\ (\y. y /\ z) q /\ (x = a) /\ r x z”
  val ub_beta_applied_t = “?x:'a. p x /\ (q /\ z) /\ x = a /\ r x z”
  fun mkC ss sl = QCONV (SIMP_CONV (del ss sl) [])
  fun mktag s = "rewrite deletion: " ^ s
  fun mkex_tag s = "deletion via Excl: " ^ s
  fun mkexsf_tag s = "deletion via ExclSF: " ^ s
  fun mktest ss (t,dels) = mkC ss dels t
  fun mkexcltest (dels, t) =
      QCONV (SIMP_CONV bool_ss (map Excl ("bool_case_thm" :: dels))) t
  fun mkexclsftest (dels, t) =
      QCONV (SIMP_CONV booleta_ss (map ExclSF dels)) t
  fun test0 (s,l,ss,t1,t2) =
      (tprint s;
       require_msg (check_result (aconv t2 o rhs o concl))
                   (term_to_string o concl)
                   (mktest ss) (t1,l))
  fun test (s,l,t1,t2) = test0(s,l,bool_ss,t1,t2)
  fun excltest (s,l,t1,t2) =
      (tprint s;
       require_msg (check_result (aconv t2 o rhs o concl))
                   (term_to_string o concl)
                   mkexcltest (l, t1))
  fun exclsftest (s,l,t1,t2) =
      (tprint s;
       require_msg (check_result (aconv t2 o rhs o concl))
                   (term_to_string o concl)
                   mkexclsftest(l,t1))
  fun rmsfs (s, ss, rms, t1, t2) =
      (tprint ("Fragment removal: "^s);
       require_msg (check_result (aconv t2 o rhs o concl))
                   (term_to_string o concl)
                   (QCONV (SIMP_CONV (remove_ssfrags rms ss) [])) t1)
in
  List.app (ignore o test) [
    (mktag "bool_ss -* COND_CLAUSES (1)", ["COND_CLAUSES"], T_t, T_t),
    (mktag "bool_ss -* COND_CLAUSES (2)", ["COND_CLAUSES"], F_t, F_t),
    (mktag "bool_ss -* bool$COND_CLAUSES is a no-op",
     ["bool$COND_CLAUSES"], T_t, “p:'b”),
    (mktag "bool_ss -* COND_CLAUSES.1", ["COND_CLAUSES.1"], T_t, T_t),
    (mktag "bool_ss -* COND_CLAUSES.2", ["COND_CLAUSES.2"], T_t, “p:'b”),
    (mktag "bool_ss -* BETA_CONV", ["BETA_CONV"], beta_t, beta_t),
    (mktag "bool_ss -* UNWIND_EXISTS_CONV", ["UNWIND_EXISTS_CONV"],
     unwind_t, unwind_t)
  ];
  List.app (ignore o test0) [
    (mktag "rmfrags [\"UNWIND\"] bool_ss -* BETA_CONV", ["BETA_CONV"],
     remove_ssfrags ["UNWIND"] bool_ss, unwind_beta_t, unwind_beta_t)
  ];
  List.app (ignore o test0) [
    (mktag "rmfrags [\"UNWIND\"] (bool_ss -* BETA_CONV)", [],
     remove_ssfrags ["UNWIND"] (bool_ss -* ["BETA_CONV"]),
     unwind_beta_t, unwind_beta_t)
  ];
  List.app (ignore o excltest) [
    (mkex_tag "bool_ss & \"COND_CLAUSES.1\"", ["COND_CLAUSES.1"],
     T_t, T_t),
    (mkex_tag "bool_ss & \"BETA_CONV\"", ["BETA_CONV"], beta_t, beta_t)
  ];
  convtest
    ("deletion via ExclX: rule:bool$COND_CLAUSES",
     QCONV (SIMP_CONV bool_ss
       [Excl "bool_case_thm",ExclX "rule:bool$COND_CLAUSES"]), T_t, T_t);
  List.app (ignore o exclsftest) [
    (mkexsf_tag "booleta_ss & ETA_ss", ["ETA"], eta_t, eta_t),
    (mkexsf_tag "booleta_ss & UNWIND_ss", ["UNWIND"], unwind_beta_t,
     ub_beta_applied_t),
    (mkexsf_tag "booleta_ss & UNWIND_ss", ["UNWIND"], unwind_t, unwind_t),
    (mkexsf_tag "booleta_ss & CONG_ss", ["CONG"], “if p /\ q then p else q”,
     “if p /\ q then p else q”)
  ];
  List.app (ignore o rmsfs) [
    ("UNWIND", bool_ss, ["UNWIND"], unwind_t, unwind_t),
    ("UNWIND on (bool_ss -* [\"BETA_CONV\"]) 1", bool_ss -* ["BETA_CONV"],
     ["UNWIND"], beta_t, beta_t),
    ("UNWIND on (bool_ss -* [\"BETA_CONV\"]) 2", bool_ss -* ["BETA_CONV"],
     ["UNWIND"], unwind_beta_t, unwind_beta_t)
  ]
end;

fun printgoal (asms,w) =
    "([" ^ String.concatWith "," (map term_to_string asms) ^ "], " ^
    term_to_string w ^ ")"
fun printgoals (sgs, _) =
    "[" ^ String.concatWith ",\n" (map printgoal sgs) ^ "]"


(* flavours of Req* *)
val _ = let
  open pureSimps
  val oneone_asm = [“ONE_ONE (f:'a -> 'b)”]
  fun req_test (nm,thl,asms,i,oopt) =
      let
        val _ = tprint nm
        val testresult =
            case oopt of
                NONE => (fn r => case r of Exn.Exn _ => true | _ => false)
              | SOME t => if type_of t = alpha then
                            (fn r => case r of Exn.Res _ => true | _ => false)
                          else
                            (fn r => case r of
                                         Exn.Res (sgs,_) =>
                                           list_eq goal_eq [(asms, t)] sgs
                                       | _ => false)

      in
        require_msg testresult printgoals
                    (runtac (VALID (ASM_SIMP_TAC pure_ss thl)))
                    (asms,i)
      end
  val oneone = Q.prove(‘ONE_ONE f ==> !x y. (f x = f y) <=> (x = y)’,
                       REWRITE_TAC[ONE_ONE_THM] >> rpt strip_tac >> eq_tac >>
                       strip_tac >-
                         (first_x_assum irule >> ASM_REWRITE_TAC[]) >>
                       ASM_REWRITE_TAC[])
in
List.app (ignore o req_test) [
  ("req0 fires", [Req0 AND_CLAUSES], [], “p /\ T”, SOME “p:bool”),
  ("req0 fires trivially", [Req0 AND_CLAUSES], [], “p /\ q”, SOME “p /\ q”),
  ("reqD fires", [ReqD AND_CLAUSES], [], “p /\ T”, SOME “p:bool”),
  ("reqD fails", [ReqD AND_CLAUSES], [], “p /\ q”, NONE),
  ("req0 succeeds (cond_rwt)", [Req0 oneone], oneone_asm,
   “(f:'a -> 'b) x = f y”, SOME “x:'a = y”),
  ("req0 fails (cond_rwt)", [Req0 oneone], [], “(f:'a -> 'b) x = f y”, NONE),
  (* Legacy checks survive only on the final argument, even though every
     requirement payload is stripped and passed to the simplifier. *)
  ("reqD before unmarked is dropped", [ReqD AND_CLAUSES, TRUTH], [],
   “p /\ q”, SOME “p /\ q”),
  ("reqD after unmarked is checked", [TRUTH, ReqD AND_CLAUSES], [],
   “p /\ q”, NONE),
  ("req0 before unmarked is dropped", [Req0 oneone, TRUTH], [],
   “(f:'a -> 'b) x = f y”, SOME “(f:'a -> 'b) x = f y”),
  ("req0 after unmarked is checked", [TRUTH, Req0 oneone], [],
   “(f:'a -> 'b) x = f y”, NONE),
  ("req0/Once fails", [Req0 (Once AND_CLAUSES)], [], “p /\ T /\ q /\ T”, NONE),
  ("reqD/Once succeeds", [ReqD (Once AND_CLAUSES)], [] ,
   “p /\ T /\ q /\ T”, SOME “x:α”),
  ("req0/Twice succeeds", [Req0 (Ntimes AND_CLAUSES 2)], [],
   “p /\ T /\ q /\ T”, SOME “p /\ q”),
  ("SF ETA_ss succeeds", [SF boolSimps.ETA_ss], [], “P (\x:'a. f x:'b) /\ T”,
   SOME “P (f:'a -> 'b) /\ T”),
  ("SF ETA_ss & DNF_ss succeeds",
   [SF boolSimps.ETA_ss, AND_CLAUSES, SF boolSimps.DNF_ss], [],
   “p /\ (p \/ R (\x:'a . f x:'b))”,
   SOME “p \/ p /\ R (f : 'a -> 'b)”),
  ("SF DISJ_ss & DNF_ss succeeds",
   [SF boolSimps.DISJ_ss, AND_CLAUSES, SF boolSimps.DNF_ss], [],
   “p /\ (p \/ r)”, SOME “p \/ F”)
]
end;


val _ = let
  fun testresult outgs res =
      case res of
          Exn.Res (sgs, _) => list_eq goal_eq outgs sgs
        | _ => false
  fun test (msg, tac, ing, outgs) =
      (tprint msg;
       require_msg (testresult outgs) printgoals (runtac tac) ing)
  val T_t = “?x:'a. p”
  fun gs c = global_simp_tac c
  val fs = full_simp_tac
  val gsc = {droptrues=true,elimvars=false,strip=true,oldestfirst=true}
  val gsc' = {droptrues=true,elimvars=false,strip=true,oldestfirst=false}
  val bss1 = bool_ss ++ rewrites [ASSUME “x = T”]
  val bss2 = bss1 ++ rewrites [ASSUME “x = F”]
in
  List.app (ignore o test) [
    ("Abbrev var not rewritten",
     rev_full_simp_tac (bool_ss ++ ABBREV_ss) [],
     ([“Abbrev (v <=> q /\ r)”, “v = F”], “P (v:bool):bool”),
     [([“Abbrev (v <=> q /\ r)”, “~v”], “P F:bool”)]),
    ("simp_tac + Excl", simp_tac bool_ss [Excl "EXISTS_SIMP"], ([], T_t),
     [([], T_t)]),
    ("fs + Excl", fs bool_ss [Excl "EXISTS_SIMP"], ([], T_t),
     [([], T_t)]),
    ("gs + Excl", gs gsc bool_ss [Excl "EXISTS_SIMP"], ([], T_t),
     [([], T_t)]),
    ("gs oldestfirst", gs gsc bool_ss [], ([“x:'a = y”, “x:'a = z”], “p:bool”),
     [([“x:'a = z”, “y:'a = z”], “p:bool”)]),
    ("gs oldestfirst", gs gsc' bool_ss [],
     ([“x:'a = y”, “x:'a = z”], “p:bool”),
     [([“z:'a = y”, “x:'a = y”], “p:bool”)]),
    ("fs + Excl (in assumptions)", fs bool_ss [Excl "EXISTS_SIMP"],
     ([“^T_t = X”], “p /\ q”), [([“^T_t = X”], “p /\ q”)]),
    ("gs + Excl (in assumptions)", gs gsc bool_ss [Excl "EXISTS_SIMP"],
     ([“^T_t = X”], “p /\ q”), [([“^T_t = X”], “p /\ q”)]),
    ("NoAsms",
     asm_simp_tac bool_ss [markerLib.NoAsms],
     ([“x = F”], “p /\ x”), [([“x = F”], “p /\ x”)]),
    ("IgnAsm",
     asm_simp_tac bool_ss [markerLib.IgnAsm ‘x = _’],
     ([“x = F”, “y = T”], “p /\ x /\ y”), [([“x = F”, “y = T”], “p /\ x”)]),
    ("IgnAsm (sub-match)",
     asm_simp_tac bool_ss [markerLib.IgnAsm ‘F (* sa *)’],
     ([“x = F”, “y = T”], “p /\ x /\ y”), [([“x = F”, “y = T”], “p /\ x”)]),
    ("Rewrite competition: ASM vs arg",
     asm_simp_tac bool_ss [ASSUME “x = T”],
     ([“x = F”], “P (x:bool):bool”), [([“x = F”], “P F:bool”)]),
    ("Rewrite competition: ARG1 vs arg2",
     asm_simp_tac bool_ss [ASSUME “x = T”, ASSUME “x = F”],
     ([], “P (x:bool):bool”), [([], “P T:bool”)]),
    ("Rewrite competition: ASM1 vs asm2",
     asm_simp_tac bool_ss [],
     ([“x=T”, “x=F”], “P (x:bool):bool”), [([“x=T”,“x=F”], “P T:bool”)]),
    ("Rewrite competition: ss1 vs SS2",
     asm_simp_tac bss2 [],
     ([], “P(x:bool):bool”), [([], “P F:bool”)]),
    ("Rewrite competition: ARG vs ss",
     asm_simp_tac bss1 [ASSUME “x = F”],
     ([], “P(x:bool):bool”), [([], “P F:bool”)]),
    ("Rewrite competition: ASM vs ss",
     asm_simp_tac bss1 [],
    ([“x = F”], “P(x:bool):bool”), [([“x = F”], “P F:bool”)])
  ]
end

(* ---------------------------------------------------------------------- *)
(* Plain tactic dispatch: whole passes versus the counted-pass engine.   *)

val _ = let
  val cfg = {strip=false,elimvars=false,droptrues=false,oldestfirst=true}
  val xcfg = {base=cfg,concl_in_fixpoint=false,imp_rebuild=false,
              imp_premises=false}
  fun check msg expected tac goal =
    (tprint msg;
     require_msg (fn Exn.Res gs => list_eq goal_eq expected gs
                  | _ => false)
                 (fn gs => printgoals (gs,())) (valid tac) goal)

  (* This conversion is deliberately not idempotent: its second visit to
     a expands it. simpLib repeats the entire pass after b changes; the
     counted engine skips a, which was unchanged after b in the first
     pass. Expansion fires only once, so both schedules terminate. *)
  fun fixture () =
    let
      val a = ``dispatch_a:bool``
      val b0 = ``dispatch_b /\ T``
      val b1 = ``dispatch_b:bool``
      val c = ``dispatch_c:bool``
      val visits = ref 0
      val expanded = ref false
      fun probe _ _ tm =
        if aconv tm a then
          (visits := !visits + 1;
           if !visits = 2 andalso not (!expanded) then
             (expanded := true;
              SYM (REWRITE_CONV [AND_CLAUSES] (mk_conj (a,T))))
           else NO_CONV tm)
        else if aconv tm b0 then REWRITE_CONV [AND_CLAUSES] tm
        else NO_CONV tm
      val ss = empty_ss ++
        conv_ss {name="dispatch non-idempotent probe",key=NONE,trace=0,
                 conv=probe}
      val w = ``dispatch_goal:bool``
    in
      (ss,([a,b0,c],w),[([mk_conj(a,T),b1,c],w)],[([a,b1,c],w)])
    end
  fun old_call msg update ths =
    let val (ss,goal,whole,_) = fixture ()
    in check msg whole (global_simp_tac cfg (update ss) ths) goal end
  fun new_call msg update ths =
    let val (ss,goal,_,counted) = fixture ()
    in check msg counted (global_simp_tac cfg (update ss) ths) goal end
  val _ = old_call "strategy-free global tactic repeats whole passes" I []
  val _ = let val (ss,goal,_,counted) = fixture ()
          in check "explicit GEN_GLOBAL_SIMP_TAC keeps counted passes"
               counted (GEN_GLOBAL_SIMP_TAC {safe=false} xcfg ss []) goal
          end
  val _ = old_call "bare Excl preserves the ordinary global schedule" I
                   [Excl "dispatch_unmatched_rule"]
  val plain_frag = name_ss "dispatch strategy-free fragment" (rewrites [])
  val _ = old_call "strategy-free SF preserves the ordinary schedule" I
                   [SF plain_frag]

  val failing_solver = mk_tactic_solver ("dispatch solver",NO_TAC)
  fun preserving_subgoaler ({recurse,...} : Traverse.simp_prover_ctxt) =
    recurse
  val _ = List.app
    (fn (name,update) => new_call ("global dispatch: " ^ name) update [])
    [("looper",add_looper ("dispatch looper",K NO_TAC)),
     ("unsafe solver",add_unsafe_solver failing_solver),
     ("safe solver",add_safe_solver failing_solver),
     ("subgoaler",set_subgoaler preserving_subgoaler),
     ("condition depth",set_cond_depth 4),
     ("term order",set_term_ord Cond_rewr.ac_term_ord)]
  val loop_frag = name_ss "dispatch looper fragment"
                   (looper_ss ("dispatch fragment looper",K NO_TAC))
  val unsafe_frag = name_ss "dispatch unsafe fragment"
                     (solver_ss failing_solver)
  val safe_frag = name_ss "dispatch safe fragment"
                   (safe_solver_ss failing_solver)
  val _ = List.app
    (fn (name,th) => new_call ("global dispatch: " ^ name) I [th])
    [("SF looper",SF loop_frag),
     ("SF unsafe solver",SF unsafe_frag),
     ("SF safe solver",SF safe_frag),
     ("Req0 SF looper",Req0 (SF loop_frag)),
     ("Once SF looper",Once (SF loop_frag))]

  val solved_tm = ``dispatch_solver_p \/ ~dispatch_solver_p``
  val solved_th = SPEC ``dispatch_solver_p:bool`` boolTheory.EXCLUDED_MIDDLE
  val solving_frag = name_ss "dispatch solving fragment"
    (solver_ss (mk_tactic_solver
       ("dispatch fragment solver",ACCEPT_TAC solved_th)))
  val _ = check "ASM_SIMP_TAC dispatches a solver-bearing SF" []
    (ASM_SIMP_TAC empty_ss [SF solving_frag]) ([],solved_tm)
  val _ = check "SIMP_TAC dispatches a requirement-wrapped solver SF" []
    (SIMP_TAC empty_ss [Req0 (SF solving_frag)]) ([],solved_tm)

  fun legacy_asm ss ths =
    markerLib.process_taclist_then{arg=ths} (CONV_TAC o SIMP_CONV ss)
  fun parity msg ths goal =
    let val expected =
          valid (legacy_asm bool_ss (markerLib.NoAsms::ths)) goal
    in check msg expected (SIMP_TAC bool_ss ths) goal end
  val _ = parity "strategy-free SIMP_TAC preserves ordinary Req0"
                   [Req0 AND_CLAUSES] ([],``dispatch_p /\ T``)
  val _ = parity "strategy-free SIMP_TAC preserves ordinary ReqD"
                   [ReqD AND_CLAUSES] ([],``dispatch_p /\ T``)
  val _ = parity "strategy-free SIMP_TAC preserves ordinary ReqD/Once"
                   [ReqD (Once AND_CLAUSES)]
                   ([],``dispatch_p /\ T /\ dispatch_q /\ T``)
in
end

(* ---------------------------------------------------------------------- *)
(* Default-equivalence goldens for the traversal solver pipeline.         *)
(* ---------------------------------------------------------------------- *)

local
  val recursive_rwt =
    Q.ASSUME `(p /\ T) ==> ((f : 'a -> 'b) x = y)`
  val failed_rwt =
    Q.ASSUME `(p /\ T) ==> ((f : 'a -> 'b) x = y)`

  val c1 = ``p = q``
  val c2 = ``(f : bool -> bool) = g``
  val c3 = ``(f : (bool -> bool) -> bool) = g``
  val c4 = ``(f : ((bool -> bool) -> bool) -> bool) = g``
  val c5 =
    ``(f : (((bool -> bool) -> bool) -> bool) -> bool) = g``

  fun cond_true condition lhs =
    ASSUME (mk_imp (condition, mk_eq (lhs, T)))

  val root_rwt =
    ASSUME
      (mk_imp (c1,
               mk_eq (``(depth_f : 'a -> 'b) depth_x``, ``depth_y : 'b``)))
  val depth4_rwts =
    [root_rwt, cond_true c2 c1, cond_true c3 c2,
     cond_true c4 c3, ASSUME (mk_eq (c4, T))]
  val depth5_rwts =
    [root_rwt, cond_true c2 c1, cond_true c3 c2,
     cond_true c4 c3, cond_true c5 c4, ASSUME (mk_eq (c5, T))]

  val no_beta_ss = bool_ss -* ["BETA_CONV"]
  val raw_bool_conv =
    Traverse.TRAVERSE (traversedata_for_ss bool_ss) []
in
  val _ = convtest
    ("default pipeline: recursive traversal proves a side condition",
     SIMP_CONV bool_ss [Q.ASSUME `p`, recursive_rwt],
     ``(f : 'a -> 'b) x``, ``y : 'b``)

  val _ = convtest
    ("default pipeline: failed side condition restores traversal limit",
     SIMP_CONV (limit 1 bool_ss) [failed_rwt],
     ``(h : 'b -> bool -> 'c) ((f : 'a -> 'b) x) (q /\ T)``,
     ``(h : 'b -> bool -> 'c) (f x) q``)

  val _ = tprint "default conditional-rewrite stack limit is four"
  val _ =
    if !Cond_rewr.stack_limit = 4 then OK()
    else die ("expected stack limit 4, got " ^
              Int.toString (!Cond_rewr.stack_limit))

  val _ = convtest
    ("default pipeline: four nested side conditions succeed",
     SIMP_CONV pureSimps.pure_ss depth4_rwts,
     ``(depth_f : 'a -> 'b) depth_x``, ``depth_y : 'b``)

  val _ = convtest
    ("default pipeline: fifth nested side condition is rejected",
     QCONV (SIMP_CONV pureSimps.pure_ss depth5_rwts),
     ``(depth_f : 'a -> 'b) depth_x``,
     ``(depth_f : 'a -> 'b) depth_x``)

  val unchanged_tm = ``(unchanged_f : 'a -> 'b) unchanged_x``

  val _ = shouldfail
    {testfn = raw_bool_conv,
     printresult = thm_to_string,
     printarg = K "raw traversal maps congruence UNCHANGED to HOL_ERR",
     checkexn = fn HOL_ERR _ => true | _ => false}
    unchanged_tm

  val _ = shouldfail
    {testfn = SIMP_CONV bool_ss [],
     printresult = thm_to_string,
     printarg = K "public conversion propagates unchanged result",
     checkexn = fn Conv.UNCHANGED => true | _ => false}
    unchanged_tm

  val _ = let
    (* This is the ordinary public destructor pin, not a lifted view. *)
    open OrdinarySimp OrdinaryBool
    val d = traversedata_for_ss bool_ss
    val {name,initial,addcontext,apply} =
      OrdinaryTraverse.dest_reducer (hd (#rewriters d))
    val r = OrdinaryTraverse.REDUCER
      {name=name, initial=initial, addcontext=addcontext, apply=apply}
  in
    convtest ("dest_reducer reads simpLib's context rewriter",
              OrdinaryTraverse.TRAVERSE
                {limit= #limit d, rewriters=[r], dprocs= #dprocs d,
                 travrules= #travrules d, relation= #relation d} [],
              ``p /\ T``, ``p:bool``)
  end

  val _ = convtest
    ("default pipeline: QCONV turns unchanged result into reflexivity",
     QCONV (SIMP_CONV bool_ss []), unchanged_tm, unchanged_tm)

  val _ = convtest
    ("default pipeline: unchanged operator preserves changed argument",
     SIMP_CONV bool_ss [],
     ``(unchanged_f : bool -> 'a) (p /\ T)``,
     ``(unchanged_f : bool -> 'a) p``)

  val _ = convtest
    ("default pipeline: changed operator preserves unchanged argument",
     SIMP_CONV bool_ss [],
     ``(unchanged_f : bool -> 'a -> 'b) (p /\ T) unchanged_x``,
     ``(unchanged_f : bool -> 'a -> 'b) p unchanged_x``)

  val _ = convtest
    ("default pipeline: implication context rewrites its consequent",
     SIMP_CONV bool_ss [], ``p ==> p /\ q``, ``p ==> q``)

  val _ = convtest
    ("default pipeline: let context rewrites its body",
     SIMP_CONV no_beta_ss [Cong boolTheory.LET_CONG],
     ``let x : 'a = a in if x = a then y : 'b else z``,
     ``let x : 'a = a in y : 'b``)

  exception EMPTY_CONTEXT
  val prover_error = mk_HOL_ERR "selftest" "toy_solver"
  val excluded_middle =
    SPEC ``toy_p (toy_x : 'a) : bool`` boolTheory.EXCLUDED_MIDDLE
  val solver_rwt =
    ASSUME
      ``(toy_p (toy_x : 'a) \/ ~toy_p toy_x) ==>
        ((toy_f : 'a -> 'b) toy_x = toy_y)``
  fun excluded_middle_solver _ tm =
    if aconv tm (concl excluded_middle) then excluded_middle
    else raise prover_error "Condition not recognized"
  val toy_solver =
    {name="excluded middle", solve=excluded_middle_solver}
  val solver_rewr =
    Cond_rewrExt.COND_REWR_CONV_WITH_CONTEXT ("solver_rwt",solver_rwt) false
  val solver_reducer =
    Traverse.CONTEXT_REDUCER
      {name=SOME "solver test reducer",
       initial=EMPTY_CONTEXT,
       addcontext=fn (ctxt,_) => ctxt,
       apply=fn {solver,stack,cond_depth,term_ord,...} =>
         solver_rewr
           {solver=solver, stack=stack, cond_depth=cond_depth,
            term_ord=term_ord}}
  val pure_data = #1 (xtraversedata_for_ss pureSimps.pure_ss)

  (* The entry points that take traversal-strategy settings take them
     alongside the traverse_data, so the tests below pair the two. *)
  fun with_reducers (data : Traverse.traverse_data) rewriters dprocs limit
      : Traverse.traverse_data =
    {rewriters=rewriters, dprocs=dprocs, limit=limit,
     relation= #relation data, travrules= #travrules data}
  fun configure_data (data : Traverse.traverse_data)
                     subgoaler solvers cond_depth term_ord
      : Traverse.xtraverse_data =
    (data, {subgoaler=subgoaler, solvers=solvers,
            cond_depth=cond_depth, term_ord=term_ord})

  val visited = ref ([] : term list)
  val visit_error =
    mk_HOL_ERR "selftest" "child_first_visit" "probe only"
  val visit_reducer =
    lifted_reducer
      {name=SOME "child-first visit probe",
       initial=EMPTY_CONTEXT,
       addcontext=fn (context, _) => context,
       apply=fn _ => fn tm =>
         (visited := tm :: !visited; raise visit_error)}
  val visit_data =
    configure_data (with_reducers pure_data [visit_reducer] [] NONE)
                   NONE [] NONE NONE
  val visit_term =
    ``(visit_outer : bool -> bool)
        ((visit_inner : bool -> bool) visit_value)``
  val visit_child =
    ``(visit_inner : bool -> bool) visit_value``
  fun visits conversion =
    (visited := [];
     ignore (QCONV (TRY_CONV conversion) visit_term);
     List.rev (!visited))
  fun precedes first second [] = false
    | precedes first second (term :: later) =
        if aconv first term then List.exists (aconv second) later
        else precedes first second later
  val default_visits = visits (Traverse.XTRAVERSE visit_data [])
  val child_charges = ref 0
  val child_visits =
    visits
      (Traverse.TRAVERSE_WITH_CONTEXT
         (Traverse.ChildFirst
            (Traverse.charge_only
               (fn () => child_charges := !child_charges + 1)))
         visit_data
         {reducer_context=[], solver_context=[]})
  val _ =
    (tprint "opt-in traversal visits children before parent reducers";
     if precedes visit_term visit_child default_visits andalso
        precedes visit_child visit_term child_visits andalso
        !child_charges > 0
     then OK () else die "child-first traversal order changed")

  exception ChildWorkLimit
  val _ =
    (tprint "child-first traversal propagates a work cutoff";
     if ((ignore
            (Traverse.TRAVERSE_WITH_CONTEXT
               (Traverse.ChildFirst
                  (Traverse.charge_only (fn () => raise ChildWorkLimit)))
               visit_data {reducer_context=[], solver_context=[]}
               visit_term);
          false)
         handle ChildWorkLimit => true)
     then OK () else die "child-first work cutoff was swallowed")

  val child_bool_conv =
    QCONV
      (Traverse.TRAVERSE_WITH_CONTEXT
         (Traverse.ChildFirst (Traverse.charge_only (fn () => ())))
         (xtraversedata_for_ss bool_ss)
         {reducer_context=[], solver_context=[]})
  val _ = convtest
    ("child-first congruence passes a premise to its consequent",
     child_bool_conv, ``p ==> p /\ q``, ``p ==> q``)
  val _ = convtest
    ("opt-in child-first simplifier conversion is public",
     SIMP_CONV_CHILD_FIRST (Traverse.charge_only (fn () => ())) bool_ss [],
     ``p ==> p /\ q``, ``p ==> q``)
  val _ = convtest
    ("child-first keeps an eta function head before descent",
     SIMP_CONV_CHILD_FIRST (Traverse.charge_only (fn () => ())) empty_ss [],
     ``(h:('a -> 'b) -> 'c) (\x:'a. (f:'a -> 'b) x)``,
     ``(h:('a -> 'b) -> 'c) (f:'a -> 'b)``)
  val eta_hcong =
    Tactical.prove
      (``!f f' c c' k k'. (f = f') /\ (c:'a = c') /\ (k:'a->bool = k') ==>
           ((eh:('a->'a)->'a->('a->bool)->'a) f c k = eh f' c' k')``,
       SIMP_TAC bool_ss [])
  val _ = convtest
    ("child-first eta head survives a later non-eta abstraction",
     SIMP_CONV_CHILD_FIRST (Traverse.charge_only (fn () => ()))
       (pureSimps.pure_ss ++ SSFRAG {name=NONE, convs=[], rewrs=[], ac=[],
          filter=NONE, dprocs=[], congs=[eta_hcong]})
       [ASSUME ``!x:'a. (ef:'a->'a) x = eg x``,
        ASSUME ``!c (k:'a->bool).
                   (eh:('a->'a)->'a->('a->bool)->'a) ef c k = c``],
     ``(eh:('a->'a)->'a->('a->bool)->'a) (\x. ef x) c (\y. y = z /\ p)``,
     ``c:'a``)
  val _ = convtest
    ("child-first does not eta-contract a quantifier predicate",
     QCONV (SIMP_CONV_CHILD_FIRST
              (Traverse.charge_only (fn () => ())) empty_ss []),
     ``!x:'a. P x``, ``!x:'a. P x``)
  val _ =
    (tprint "child-first simplifier conversion propagates its budget";
     if ((ignore
            (SIMP_CONV_CHILD_FIRST
               (Traverse.charge_only (fn () => raise ChildWorkLimit))
               bool_ss []
               ``p /\ T``);
          false)
         handle ChildWorkLimit => true)
     then OK () else die "child-first simplifier budget was swallowed")

  val overlap_rules =
    [Tactical.prove
       (``~(p /\ T) = (p ==> F)``, SIMP_TAC bool_ss []),
     Tactical.prove (``(p /\ T) = p``, SIMP_TAC bool_ss []),
     Tactical.prove (``(~p) = (p = F)``, SIMP_TAC bool_ss [])]
  val overlap_term = ``~(q /\ T)``
  val _ = convtest
    ("default traversal takes the parent overlap first",
     SIMP_CONV pureSimps.pure_ss overlap_rules,
     overlap_term, ``q ==> F``)
  val _ = convtest
    ("child-first traversal gives the normalized child to its parent",
     SIMP_CONV_CHILD_FIRST (Traverse.charge_only (fn () => ()))
       pureSimps.pure_ss overlap_rules,
     overlap_term, ``q = F``)
  val _ =
    (tprint "child-first tactic simplifies the conclusion";
     case valid
            (GEN_SIMP_TAC_CHILD_FIRST
               (Traverse.charge_only (fn () => ())) {safe=false}
               pureSimps.pure_ss overlap_rules)
            ([], overlap_term) of
         [([], result)] =>
           if aconv result ``q = F`` then OK ()
           else die "child-first tactic left the wrong conclusion"
       | _ => die "child-first tactic changed the goal shape")
  val child_global_config : xsimptac_config =
    {base={strip=false, elimvars=false, droptrues=false,
           oldestfirst=true},
     concl_in_fixpoint=true, imp_rebuild=false, imp_premises=false}
  val _ =
    (tprint "child-first global tactic uses the same traversal";
     case valid
            (GEN_GLOBAL_SIMP_TAC_CHILD_FIRST
               (Traverse.charge_only (fn () => ()))
               {safe=false} child_global_config
               pureSimps.pure_ss overlap_rules)
            ([], overlap_term) of
         [([], result)] =>
           if aconv result ``q = F`` then OK ()
           else die "child-first global tactic left the wrong result"
       | _ => die "child-first global tactic changed the goal shape")

  val solver_data =
    configure_data (with_reducers pure_data [solver_reducer] [] NONE)
                   NONE [toy_solver] NONE NONE
  val solver_conv = Traverse.XTRAVERSE solver_data []

  val _ = convtest
    ("solver pipeline: unsafe solver proves residual condition",
     solver_conv, ``(toy_f : 'a -> 'b) toy_x``, ``toy_y : 'b``)

  val context_rwt =
    ASSUME ``context_p ==> ((context_f : 'a -> 'b) context_x = context_y)``
  val context_rewr =
    Cond_rewrExt.COND_REWR_CONV_WITH_CONTEXT ("context_rwt",context_rwt) false
  val context_reducer =
    Traverse.CONTEXT_REDUCER
      {name=SOME "context test reducer",
       initial=EMPTY_CONTEXT,
       addcontext=fn (ctxt,_) => ctxt,
       apply=fn {solver,stack,cond_depth,term_ord,...} =>
         context_rewr
           {solver=solver, stack=stack, cond_depth=cond_depth,
            term_ord=term_ord}}
  val bool_data = #1 (xtraversedata_for_ss bool_ss)
  fun context_solver {context_thms,...} tm =
    case List.find (fn th => aconv tm (concl th)) context_thms of
        SOME th => th
      | NONE => raise prover_error "Condition absent from context"
  val context_data =
    configure_data (with_reducers bool_data [context_reducer] [] NONE)
                   NONE [{name="context lookup",solve=context_solver}]
                   NONE NONE
  val context_conv = Traverse.XTRAVERSE context_data []

  val _ = convtest
    ("solver pipeline: congruence context theorem is visible",
     context_conv,
     ``context_p ==> (context_f : 'a -> 'b) context_x = context_z``,
     ``context_p ==> (context_y : 'b) = context_z``)

  fun failing_solver _ _ =
    raise prover_error "Deliberate solver failure"
  val limited_data =
    configure_data
      (with_reducers bool_data (#rewriters bool_data) (#dprocs bool_data)
                     (SOME 1))
      NONE [{name="always fails",solve=failing_solver}] NONE NONE
  val solver_failure_conv = Traverse.XTRAVERSE limited_data [failed_rwt]

  val _ = convtest
    ("solver pipeline: solver failure restores traversal limit",
     solver_failure_conv,
     ``(h : 'b -> bool -> 'c) ((f : 'a -> 'b) x) (q /\ T)``,
     ``(h : 'b -> bool -> 'c) (f x) q``)

  val repeated_recurse_rwt =
    Q.ASSUME
      `(T /\ T) ==>
       ((repeated_recurse_f : 'a -> 'b) repeated_recurse_x =
        repeated_recurse_y)`
  val repeated_recurse_probe = ``repeated_recurse_probe : bool``
  fun repeated_recurse_subgoaler {recurse, ...} tm =
    let
      val solved = recurse tm
      val _ = recurse repeated_recurse_probe
    in
      solved
    end
  val repeated_recurse_data =
    configure_data
      (with_reducers bool_data (#rewriters bool_data) (#dprocs bool_data)
                     (SOME 2))
      (SOME repeated_recurse_subgoaler) [] NONE NONE
  val repeated_recurse_conv =
    Traverse.XTRAVERSE repeated_recurse_data [repeated_recurse_rwt]

  val _ = convtest
    ("solver pipeline: each recurse call restores its own limit snapshot",
     repeated_recurse_conv,
     ``(h : 'b -> bool -> 'c)
         (repeated_recurse_f repeated_recurse_x) (q /\ T)``,
     ``(h : 'b -> bool -> 'c) repeated_recurse_y (q /\ T)``)

  val exception_controls_seen = ref false
  fun passthrough_apply {solver,stack,cond_depth,term_ord,...} tm =
    if cond_depth = 31 andalso
       term_ord (boolSyntax.T, boolSyntax.F) = GREATER
    then
      (exception_controls_seen := true; solver stack tm)
    else
      raise Fail "traversal controls missing before solver exception"
  val passthrough_reducer =
    Traverse.CONTEXT_REDUCER
      {name=SOME "solver exception test reducer",
       initial=EMPTY_CONTEXT,
       addcontext=fn (ctxt,_) => ctxt,
       apply=passthrough_apply}
  fun raising_solver _ _ = raise Fail "non-HOL solver exception"
  val exception_data =
    configure_data (with_reducers bool_data [passthrough_reducer] [] NONE)
                   (SOME (fn _ => REFL))
                   [{name="raises Fail",solve=raising_solver}]
                   (SOME 31) (SOME (fn _ => GREATER))
  val exception_conv = Traverse.XTRAVERSE exception_data []

  val _ = shouldfail
    {testfn=exception_conv,
     printresult=thm_to_string,
     printarg=K "solver pipeline propagates non-HOL exceptions",
     checkexn=fn Fail "non-HOL solver exception" => true | _ => false}
    ``solver_exception_p``

  val _ = tprint "TRAVERSE passes controls before a solver exception"
  val _ =
    if !exception_controls_seen andalso !Cond_rewr.stack_limit = 4
    then OK()
    else die "configured traversal controls were not passed to the reducer"

  fun mk_depth_condition i =
    mk_eq (mk_var ("depth_l" ^ Int.toString i, Type.alpha),
           mk_var ("depth_r" ^ Int.toString i, Type.alpha))
  val depth10_conditions =
    List.tabulate (10, fn i => mk_depth_condition (i + 1))
  fun mk_depth_chain [last] = [ASSUME (mk_eq (last, boolSyntax.T))]
    | mk_depth_chain (current :: (rest as next :: _)) =
        cond_true next current :: mk_depth_chain rest
    | mk_depth_chain [] = raise Fail "empty condition chain"
  val depth10_root =
    ASSUME
      (mk_imp (hd depth10_conditions,
               mk_eq (``(depth10_f : 'a -> 'b) depth10_x``,
                      ``depth10_y : 'b``)))
  val depth10_rwts = depth10_root :: mk_depth_chain depth10_conditions
  val depth_default_data =
    configure_data pure_data NONE [] NONE NONE
  val depth40_data =
    configure_data pure_data NONE [] (SOME 40) NONE
  val depth_default_conv =
    Traverse.XTRAVERSE depth_default_data depth10_rwts
  val depth40_conv = Traverse.XTRAVERSE depth40_data depth10_rwts
  val depth10_lhs = ``(depth10_f : 'a -> 'b) depth10_x``
  val depth10_rhs = ``depth10_y : 'b``

  fun unchanged_on_hol_err conv tm =
    conv tm handle HOL_ERR _ => REFL tm | Conv.UNCHANGED => REFL tm
  val _ = convtest
    ("cond_depth: depth ten fails at the default four",
     unchanged_on_hol_err depth_default_conv, depth10_lhs, depth10_lhs)

  val _ = convtest
    ("cond_depth: per-traversal depth forty succeeds",
     depth40_conv, depth10_lhs, depth10_rhs)

  val _ =
    Lib.with_flag (Cond_rewr.stack_limit,40)
      (fn () =>
          convtest
            ("cond_depth: NONE honors the global stack limit",
             depth_default_conv, depth10_lhs, depth10_rhs)) ()

  val _ = tprint "cond_depth binding restores the global stack limit"
  val _ =
    if !Cond_rewr.stack_limit = 4 then OK()
    else die "cond_depth did not restore the global stack limit"

  (* R5: only baseline APIs.  Keep the target atomic so failed rewriting
     cannot descend and retry the root with a newly sampled depth.  The
     fixed key and shared fragment put the failing user candidate before
     the native conditional rewrite in the same reducer application. *)
  val _ = let
    val target = ``r5_depth_target : bool``
    val condition = ``r5_depth_condition : bool``
    val attempts = ref 0
    val saved_depth = !Cond_rewr.stack_limit
    fun mutate_depth _ _ _ =
      (attempts := !attempts + 1;
       Cond_rewr.stack_limit := 4;
       raise mk_HOL_ERR "selftest" "r5_mutate_depth" "try next candidate")
    val fragment =
      SSFRAG
        {name=NONE, congs=[], ac=[], filter=NONE, dprocs=[],
         convs=[{name="R5 failing depth mutation",
                 key=SOME ([target],target), trace=0, conv=mutate_depth}],
         rewrs=[(NONE,ASSUME (mk_imp (condition, mk_eq (target,T))))]}
    val ss = pureSimps.pure_ss ++ fragment
    val facts = [ASSUME (mk_eq (condition,T))]
    val _ = Lib.with_flag (Cond_rewr.stack_limit,0)
      (fn () => convtest
        ("cond_depth: NONE is live between native rewrite candidates",
         SIMP_CONV ss facts, target, T)) ()
    val _ = tprint "cond_depth: failing mutation ran once and restored depth"
  in
    if !attempts = 1 andalso !Cond_rewr.stack_limit = saved_depth then OK()
    else die "R5 candidate ordering or depth restoration failed"
  end

  (* The same mutation must not override an invocation-local integer. *)
  val _ = let
    val target = ``r5_configured_depth_target : bool``
    val condition = ``r5_configured_depth_condition : bool``
    val attempts = ref 0
    fun mutate_depth _ _ _ =
      (attempts := !attempts + 1;
       Cond_rewr.stack_limit := 4;
       raise mk_HOL_ERR "selftest" "r5_mutate_depth" "try next candidate")
    val fragment =
      SSFRAG
        {name=NONE, congs=[], ac=[], filter=NONE, dprocs=[],
         convs=[{name="R5 configured failing depth mutation",
                 key=SOME ([target],target), trace=0, conv=mutate_depth}],
         rewrs=[(NONE,ASSUME (mk_imp (condition, mk_eq (target,T))))]}
    val ss = set_cond_depth 0 (pureSimps.pure_ss ++ fragment)
    val _ = Lib.with_flag (Cond_rewr.stack_limit,0)
      (fn () => convtest
        ("cond_depth: configured zero ignores candidate default mutation",
         QCONV (SIMP_CONV ss [ASSUME (mk_eq (condition,T))]),
         target, target)) ()
    val _ = tprint "cond_depth: configured mutation candidate was attempted"
  in
    if !attempts = 1 then OK()
    else die "R5 configured candidate ordering failed"
  end

  fun reverse_order pair =
    case Cond_rewr.ac_term_ord pair of
        LESS => GREATER
      | EQUAL => EQUAL
      | GREATER => LESS
  val reverse_order_data =
    configure_data pure_data NONE [] NONE (SOME reverse_order)
  val reverse_order_conv =
    Traverse.XTRAVERSE reverse_order_data [boolTheory.EQ_SYM_EQ]
  val default_order_conv =
    Traverse.XTRAVERSE depth_default_data [boolTheory.EQ_SYM_EQ]

  val _ = convtest
    ("term_ord: default order chooses the ascending equality",
     default_order_conv, ``nested_y:'a = nested_x``,
     ``nested_x:'a = nested_y``)

  val _ = convtest
    ("term_ord: custom order flips the equality normal form",
     reverse_order_conv, ``nested_x:'a = nested_y``,
     ``nested_y:'a = nested_x``)

  val once_order_data =
    configure_data pure_data NONE [] NONE (SOME (fn _ => LESS))
  val once_order_conv =
    Traverse.XTRAVERSE once_order_data [Once boolTheory.EQ_SYM_EQ]

  val _ = convtest
    ("term_ord: Once bypasses a custom rejecting order",
     once_order_conv, ``once_x:'a = once_y``, ``once_y:'a = once_x``)

  val _ = convtest
    ("XTRAVERSE refreshes Once for each conversion application",
     once_order_conv, ``once_u:'a = once_v``, ``once_v:'a = once_u``)

  val order_probe = (``nested_order_x:'a``, ``nested_order_y:'a``)

  (* A traversal whose simpset configures neither knob must run at the
     documented defaults even when a traversal that did configure them is
     still on the stack: aesop/clasimp set cond_depth 40, and a nested
     SIMP_CONV bool_ss [] used to inherit it and recurse ten levels deeper
     than SIMP_TAC bool_ss [] does on its own. *)
  val leak_depth_result = ref (NONE : thm option)
  val leak_order_result = ref (NONE : thm option)
  val leak_controls_result = ref (~1, EQUAL)
  val leak_order_lhs = ``nested_y:'a = nested_x``
  val leak_outer_lhs = ``(leak_f : 'a -> 'b) leak_x``
  val leak_outer_rhs = ``leak_y:'b``
  val leak_outer_rwt = ASSUME (mk_eq (leak_outer_lhs,leak_outer_rhs))

  (* The controls have to be observed by a reducer in the nested traversal,
     rather than by the outer reducer. *)
  val leak_probe_lhs = ``leak_probe_x:'a``
  fun leak_controls_apply {cond_depth,term_ord,...} tm =
    (leak_controls_result := (cond_depth,term_ord order_probe);
     NO_CONV tm)
  val leak_controls_reducer =
    Traverse.CONTEXT_REDUCER
      {name=SOME "nested traversal control probe", initial=EMPTY_CONTEXT,
       addcontext=fn (ctxt,_) => ctxt, apply=leak_controls_apply}
  val leak_controls_data =
    configure_data (with_reducers pure_data [leak_controls_reducer] [] NONE)
                   NONE [] NONE NONE
  val leak_controls_conv = Traverse.XTRAVERSE leak_controls_data []

  fun leak_outer_apply _ tm =
    if not (aconv tm leak_outer_lhs) then NO_CONV tm
    else
      (leak_depth_result :=
         SOME (unchanged_on_hol_err depth_default_conv depth10_lhs);
       leak_order_result :=
         SOME (unchanged_on_hol_err default_order_conv leak_order_lhs);
       unchanged_on_hol_err leak_controls_conv leak_probe_lhs;
       leak_outer_rwt)
  val leak_outer_reducer =
    Traverse.CONTEXT_REDUCER
      {name=SOME "cond_depth/term_ord leak probe", initial=EMPTY_CONTEXT,
       addcontext=fn (ctxt,_) => ctxt, apply=leak_outer_apply}
  val leak_outer_data =
    configure_data (with_reducers pure_data [leak_outer_reducer] [] NONE)
                   NONE [] (SOME 40) (SOME reverse_order)
  val leak_outer_conv = Traverse.XTRAVERSE leak_outer_data []

  val _ = convtest
    ("nested traversal probe runs under cond_depth forty",
     leak_outer_conv, leak_outer_lhs, leak_outer_rhs)

  val _ = tprint "nested traversal does not inherit an outer cond_depth"
  val _ =
    case !leak_depth_result of
        NONE => die "leak probe did not run"
      | SOME th =>
          if aconv (rhs (concl th)) depth10_lhs then OK()
          else die "nested traversal inherited the outer stack limit"

  val _ = tprint "nested traversal does not inherit an outer term_ord"
  val _ =
    case !leak_order_result of
        NONE => die "leak probe did not run"
      | SOME th =>
          if aconv (rhs (concl th)) ``nested_x:'a = nested_y`` then OK()
          else die "nested traversal inherited the outer term order"

  val _ = tprint "nested traversal receives its own default controls"
  val _ =
    if !leak_controls_result = (4, Cond_rewr.ac_term_ord order_probe)
    then OK()
    else die "nested traversal received the outer traversal's controls"

  (* The user-level globals are what an unconfigured traversal falls back
     to, so raising Cond_rewr.stack_limit still reaches a traversal nested
     inside one that set its own depth (examples/arm relies on the global
     reaching ordinary simpsets). *)
  val _ = tprint "nested traversal honours the global stack limit"
  val _ =
    Lib.with_flag (Cond_rewr.stack_limit,40)
      (fn () =>
          (leak_outer_conv leak_outer_lhs;
           case !leak_depth_result of
               NONE => die "leak probe did not run"
             | SOME th =>
                 if aconv (rhs (concl th)) depth10_rhs then OK()
                 else die "global stack limit did not reach the nested \
                          \traversal")) ()

  val nested_inner_condition =
    SPEC ``nested_inner_q:bool`` boolTheory.EXCLUDED_MIDDLE
  val nested_inner_lhs =
    ``(nested_inner_f : 'a -> 'b) nested_inner_x``
  val nested_inner_rhs = ``nested_inner_y:'b``
  val nested_inner_rwt =
    ASSUME
      (mk_imp (concl nested_inner_condition,
               mk_eq (nested_inner_lhs,nested_inner_rhs)))
  val nested_inner_controls_seen = ref false
  fun nested_inner_apply
        {solver,stack,cond_depth,term_ord,...} tm =
    if not (aconv tm nested_inner_lhs) then NO_CONV tm
    else if cond_depth <> 23 orelse
            term_ord order_probe <> Cond_rewr.ac_term_ord order_probe
    then raise Fail "inner traversal controls missing"
    else
      (nested_inner_controls_seen := true;
       MP nested_inner_rwt (solver stack (concl nested_inner_condition)))
  val nested_inner_reducer =
    Traverse.CONTEXT_REDUCER
      {name=SOME "nested inner rewrite", initial=EMPTY_CONTEXT,
       addcontext=fn (ctxt,_) => ctxt, apply=nested_inner_apply}
  val inner_simp_tm = boolSyntax.T
  fun nested_inner_solver _ tm =
    if not (aconv tm (concl nested_inner_condition)) then
      raise Fail "inner solver received an unexpected condition"
    else let
      val simp_th = QCONV (SIMP_CONV bool_ss []) inner_simp_tm
      val _ = aconv (rhs (concl simp_th)) boolSyntax.T orelse
              raise Fail "inner solver's SIMP_CONV failed"
    in
      nested_inner_condition
    end
  val nested_inner_data =
    configure_data (with_reducers pure_data [nested_inner_reducer] [] NONE)
                   (SOME (fn _ => REFL))
                   [{name="nested inner",solve=nested_inner_solver}]
                   (SOME 23) (SOME Cond_rewr.ac_term_ord)
  val nested_inner_conv = Traverse.XTRAVERSE nested_inner_data []
  val nested_outer_lhs =
    ``(nested_outer_f : bool -> bool) nested_outer_x``
  val nested_outer_rhs = ``nested_outer_y:bool``
  val nested_outer_rwt =
    ASSUME (mk_eq (nested_outer_lhs,nested_outer_rhs))
  val nested_outer_controls_seen = ref false
  fun nested_outer_apply {cond_depth,term_ord,...} tm =
    if not (aconv tm nested_outer_lhs) then NO_CONV tm
    else let
      val _ =
        if cond_depth = 17 andalso term_ord order_probe =
           reverse_order order_probe
        then nested_outer_controls_seen := true
        else raise Fail "outer traversal controls missing"
      val nested_th =
        nested_inner_conv nested_inner_lhs
        handle HOL_ERR _ => raise Fail "inner TRAVERSE raised HOL_ERR"
      val _ = aconv (rhs (concl nested_th)) nested_inner_rhs orelse
              raise Fail "inner TRAVERSE failed"
    in
      nested_outer_rwt
    end
  val nested_outer_reducer =
    Traverse.CONTEXT_REDUCER
      {name=SOME "nested outer rewrite", initial=EMPTY_CONTEXT,
       addcontext=fn (ctxt,_) => ctxt, apply=nested_outer_apply}
  val nested_outer_data =
    configure_data (with_reducers pure_data [nested_outer_reducer] [] NONE)
                   NONE [] (SOME 17) (SOME reverse_order)
  val nested_outer_conv = Traverse.XTRAVERSE nested_outer_data []

  val _ = convtest
    ("nested TRAVERSE calls keep independent traversal controls",
     nested_outer_conv, nested_outer_lhs, nested_outer_rhs)

  val _ = tprint "both nested reducers received their own controls"
  val _ =
    if !nested_inner_controls_seen andalso !nested_outer_controls_seen andalso
       !Cond_rewr.stack_limit = 4
    then OK()
    else die "nested TRAVERSE calls mixed their traversal controls"

  val conglib_rwt =
    ASSUME ``(conglib_f : 'a -> 'b) conglib_x = conglib_y``
  val conglib_cs =
    congLib.mk_congset [congLib.csfrag_rewrites [conglib_rwt]]
  val _ = convtest
    ("congLib equality simplification smoke test",
     congLib.CONGRUENCE_EQ_SIMP_CONV conglib_cs pureSimps.pure_ss [],
     ``(conglib_f : 'a -> 'b) conglib_x``, ``conglib_y:'b``)

  val conglib_condition =
    SPEC ``conglib_solver_p:bool`` boolTheory.EXCLUDED_MIDDLE
  val conglib_solver_lhs =
    ``(conglib_solver_f : 'a -> 'b) conglib_solver_x``
  val conglib_solver_rhs = ``conglib_solver_y:'b``
  val conglib_solver_rwt =
    ASSUME
      (mk_imp (concl conglib_condition,
               mk_eq (conglib_solver_lhs,conglib_solver_rhs)))
  val conglib_solver_cs = congLib.mk_congset []
  val conglib_subgoaler_calls = ref 0
  val conglib_solver_calls = ref 0
  val conglib_controls_seen = ref false
  fun conglib_subgoaler _ tm =
    (conglib_subgoaler_calls := !conglib_subgoaler_calls + 1; REFL tm)
  fun conglib_solver _ tm =
    let
      val _ = conglib_solver_calls := !conglib_solver_calls + 1
    in
      if aconv tm (concl conglib_condition) then
        conglib_condition
      else raise prover_error "congLib traversal controls missing"
    end
  fun conglib_solver_apply
        {solver,stack,cond_depth,term_ord,...} tm =
    if not (aconv tm conglib_solver_lhs) then NO_CONV tm
    else if cond_depth <> 29 orelse
            term_ord (``conglib_order_x:'a``,
                      ``conglib_order_y:'a``) <> GREATER
    then raise prover_error "congLib traversal controls missing"
    else
      (conglib_controls_seen := true;
       MP conglib_solver_rwt
          (solver stack (concl conglib_condition)))
  val conglib_solver_reducer =
    Traverse.CONTEXT_REDUCER
      {name=SOME "congLib traversal controls",
       initial=EMPTY_CONTEXT,
       addcontext=fn (ctxt,_) => ctxt,
       apply=conglib_solver_apply}
  val conglib_solver_ss =
    pureSimps.pure_ss ++ dproc_ss conglib_solver_reducer
    |> set_subgoaler conglib_subgoaler
    |> add_unsafe_solver
         {name="congLib traversal solver",solve=conglib_solver}
    |> set_cond_depth 29
    |> set_term_ord (fn _ => GREATER)
  val _ = convtest
    ("congLib forwards simpset traversal controls",
     congLib.CONGRUENCE_EQ_SIMP_CONV
       conglib_solver_cs conglib_solver_ss [],
     conglib_solver_lhs,conglib_solver_rhs)
  val _ = tprint "congLib used the configured subgoaler and solver"
  val _ =
    if !conglib_subgoaler_calls = 1 andalso !conglib_solver_calls = 1 andalso
       !conglib_controls_seen
    then
      OK()
    else die "congLib dropped a configured traversal control"
end

(* ---------------------------------------------------------------------- *)
(* simpLib strategy fields, fragment merges, and history rebuilding.      *)
(* ---------------------------------------------------------------------- *)

fun pp ss = PP.pp_to_string 200 simpLib.pp_simpset ss

  fun occurrences needle haystack =
    let
      val needle_n = String.size needle
      val haystack_n = String.size haystack
      fun loop i n =
        if i + needle_n > haystack_n then n
        else if String.substring(haystack,i,needle_n) = needle then
          loop (i + needle_n) (n + 1)
        else loop (i + 1) n
    in
      if needle_n = 0 then 0 else loop 0 0
    end

  fun position needle haystack =
    let
      val needle_n = String.size needle
      val haystack_n = String.size haystack
      fun loop i =
        if i + needle_n > haystack_n then NONE
        else if String.substring(haystack,i,needle_n) = needle then SOME i
        else loop (i + 1)
    in
      if needle_n = 0 then NONE else loop 0
    end

  fun check msg test =
    (tprint msg; if test () then OK() else die "FAILED!")

  val dummy_looper : simpset -> tactic = fn _ => NO_TAC
  val other_looper : simpset -> tactic = fn _ => ALL_TAC

  val loopers_added =
    empty_ss
    |> add_looper ("surface looper one",dummy_looper)
    |> add_looper ("surface looper two",dummy_looper)
    |> add_looper ("surface looper one",other_looper)
  val loopers_added_pp = pp loopers_added

  val _ = check "looper add updates by name without changing order"
    (fn () =>
       occurrences "surface looper one" loopers_added_pp = 1 andalso
       occurrences "surface looper two" loopers_added_pp = 1 andalso
       (case (position "surface looper one" loopers_added_pp,
              position "surface looper two" loopers_added_pp) of
            (SOME one,SOME two) => one < two
          | _ => false))

  val singleton_looper =
    set_looper ("surface singleton looper",dummy_looper) loopers_added
  val singleton_looper_pp = pp singleton_looper

  val _ = check "set_looper replaces the registered looper list"
    (fn () =>
       occurrences "surface singleton looper" singleton_looper_pp = 1 andalso
       occurrences "surface looper one" singleton_looper_pp = 0 andalso
       occurrences "surface looper two" singleton_looper_pp = 0)

  val no_loopers = del_looper "surface singleton looper" singleton_looper
  val _ = check "del_looper removes a looper by name"
    (fn () =>
       occurrences "surface singleton looper" (pp no_loopers) = 0)

  fun never_solver _ _ =
    raise mk_HOL_ERR "selftest" "never_solver" "not applicable"
  val unsafe_one : Traverse.ssolver =
    {name="surface unsafe one",solve=never_solver}
  val unsafe_duplicate : Traverse.ssolver =
    {name="surface unsafe one",solve=never_solver}
  val safe_one : Traverse.ssolver =
    {name="surface safe one",solve=never_solver}

  val solver_merge_ss =
    empty_ss ++ solver_ss unsafe_one ++ solver_ss unsafe_duplicate
  val solver_merge_config = traverseconfig_for_ss solver_merge_ss

  val _ = check "solver fragments append and deduplicate by name"
    (fn () =>
       case #solvers solver_merge_config of
           [{name,...}] => name = "surface unsafe one"
         | _ => false)

  val fragment_unsafe : Traverse.ssolver =
    {name="surface fragment unsafe",solve=never_solver}
  val fragment_safe : Traverse.ssolver =
    {name="surface fragment safe",solve=never_solver}
  val strategy_fragment =
    named_merge_ss "surface strategy fragment"
      [looper_ss ("surface fragment looper",dummy_looper),
       solver_ss fragment_unsafe, safe_solver_ss fragment_safe]
  val fragment_set = empty_ss ++ strategy_fragment
  val fragment_removed =
    remove_ssfrags ["surface strategy fragment"] fragment_set
  val fragment_excluded =
    exclude_ssfrags ["surface strategy fragment"] fragment_set
  val replayed_duplicate =
    fragment_set
    |> add_unsafe_solver fragment_unsafe
    |> add_safe_solver fragment_safe
    |> remove_ssfrags ["surface strategy fragment"]
  val replayed_duplicate_config = traverseconfig_for_ss replayed_duplicate

  val _ = check "history replay retains later duplicate solver additions"
    (fn () =>
       length (#solvers replayed_duplicate_config) = 1 andalso
       occurrences "surface fragment safe" (pp replayed_duplicate) = 1)

  val _ = check "history rebuild removes fragment strategy payloads"
    (fn () =>
       occurrences "surface fragment looper" (pp fragment_removed) = 0 andalso
       occurrences "surface fragment unsafe" (pp fragment_removed) = 0 andalso
       occurrences "surface fragment safe" (pp fragment_removed) = 0 andalso
       occurrences "surface fragment looper" (pp fragment_excluded) = 0 andalso
       occurrences "surface fragment unsafe" (pp fragment_excluded) = 0 andalso
       occurrences "surface fragment safe" (pp fragment_excluded) = 0)

  val both_solvers =
    empty_ss
    |> add_unsafe_solver unsafe_one
    |> add_safe_solver safe_one
  val both_solvers_pp = pp both_solvers

  val _ = check "pp_simpset prints unsafe and safe solver names"
    (fn () =>
       occurrences "surface unsafe one" both_solvers_pp = 1 andalso
       occurrences "surface safe one" both_solvers_pp = 1)

  val removed_solvers = remove_solver "surface unsafe one" both_solvers
  val removed_solvers = remove_solver "surface safe one" removed_solvers

  val _ = check "remove_solver removes names from both solver lists"
    (fn () =>
       occurrences "surface unsafe one" (pp removed_solvers) = 0 andalso
       occurrences "surface safe one" (pp removed_solvers) = 0)

  fun preserving_subgoaler
        ({recurse,...} : Traverse.simp_prover_ctxt) = recurse
  fun reverse_order pair =
    case Cond_rewr.ac_term_ord pair of
        LESS => GREATER
      | EQUAL => EQUAL
      | GREATER => LESS

  val disposable =
    named_rewrites "surface disposable"
      [ASSUME ``surface_disposable_p = T``]
  val configured =
    empty_ss ++ disposable
    |> add_looper ("surface rebuilt looper",dummy_looper)
    |> add_unsafe_solver unsafe_one
    |> add_safe_solver safe_one
    |> set_subgoaler preserving_subgoaler
    |> set_cond_depth 37
    |> set_term_ord reverse_order
  val rebuilt = remove_ssfrags ["surface disposable"] configured
  val rebuilt_config = traverseconfig_for_ss rebuilt
  val rebuilt_pp = pp rebuilt
  val order_probe = (``surface_order_x:'a``, ``surface_order_y:'a``)
  val subgoal_probe = ``surface_subgoal_x:'a``
  val prover_ctxt =
    {stack=[],context_thms=[],recurse=fn tm => REFL tm}

  val _ = check "remove_ssfrags preserves all strategy fields"
    (fn () =>
       occurrences "surface rebuilt looper" rebuilt_pp = 1 andalso
       occurrences "surface safe one" rebuilt_pp = 1 andalso
       (case #solvers rebuilt_config of
            [{name,...}] => name = "surface unsafe one"
          | _ => false) andalso
       #cond_depth rebuilt_config = SOME 37 andalso
       (case #term_ord rebuilt_config of
            SOME ord => ord order_probe = reverse_order order_probe
          | NONE => false) andalso
       (case #subgoaler rebuilt_config of
            SOME sg =>
              aconv (concl (sg prover_ctxt subgoal_probe))
                    (mk_eq(subgoal_probe,subgoal_probe))
          | NONE => false))

  val cleared = clear_rules configured
  val cleared_config = traverseconfig_for_ss cleared
  val cleared_pp = pp cleared

  val _ = check "clear_rules drops loopers but keeps strategy and solvers"
    (fn () =>
       occurrences "surface rebuilt looper" cleared_pp = 0 andalso
       occurrences "surface safe one" cleared_pp = 1 andalso
       (case #solvers cleared_config of
            [{name,...}] => name = "surface unsafe one"
          | _ => false) andalso
       #cond_depth cleared_config = SOME 37 andalso
       Option.isSome (#subgoaler cleared_config) andalso
       Option.isSome (#term_ord cleared_config))

  val _ = convtest
    ("clear_rules removes ordinary rewrite rules",
     QCONV (SIMP_CONV (clear_rules bool_ss) []),
     ``surface_clear_p /\ T``, ``surface_clear_p /\ T``)

  val dropping_filter =
    SSFRAG
      {name=SOME "surface dropping filter", convs=[], rewrs=[], ac=[],
       filter=SOME (fn _ => []), dprocs=[], congs=[]}
  val empty_named = name_ss "surface post-clear fragment" empty_ssfrag
  val clear_rebuilt =
    clear_rules (mk_simpset [dropping_filter]) ++ empty_named
    |> remove_ssfrags ["surface post-clear fragment"]
  val clear_rebuilt =
    clear_rebuilt ++
    rewrites [ASSUME ``surface_filtered_x:'a = surface_filtered_y``]

  val _ = convtest
    ("clear_rules preserves mk_rewrs through later history rebuilds",
     QCONV (SIMP_CONV clear_rebuilt []),
     ``surface_filtered_x:'a``, ``surface_filtered_x:'a``)

  (* A simpset is not its fragments.  A rewrite it has removed by name is
     gone from the simpset and still stands in the fragment its history
     records, so rebuilding from [ssfrags_of] brings the rewrite back --
     along with the [excluded] set, the limit and the rewrite maker that
     rebuild drops.  [filter_rewrites] replays the history instead, so
     only the rejected rewrites go. *)
  val filter_removed_rwt = ASSUME ``surface_filter_a:'a = surface_filter_b``
  val filter_kept_rwt = ASSUME ``surface_filter_c:'a = surface_filter_d``
  val filter_base =
    empty_ss ++
      named_rewrites_with_names "surface filter probe"
        [({Thy = "scratch", Name = "surface_filter_removed"},
          filter_removed_rwt),
         ({Thy = "scratch", Name = "surface_filter_kept"},
          filter_kept_rwt)]
    |> remove_simps ["surface_filter_removed"]
  val filter_replayed = filter_rewrites (fn _ => true) filter_base
  val filter_dropped =
    filter_rewrites
      (fn (_, theorem) => not (aconv (concl theorem) (concl filter_kept_rwt)))
      filter_base

  val _ = convtest
    ("filter_rewrites keeps a rewrite the simpset removed by name removed",
     QCONV (SIMP_CONV filter_replayed []),
     ``surface_filter_a:'a``, ``surface_filter_a:'a``)

  val _ = convtest
    ("filter_rewrites keeps the rewrites the predicate accepts",
     QCONV (SIMP_CONV filter_replayed []),
     ``surface_filter_c:'a``, ``surface_filter_d:'a``)

  val _ = convtest
    ("filter_rewrites drops the rewrites the predicate rejects",
     QCONV (SIMP_CONV filter_dropped []),
     ``surface_filter_c:'a``, ``surface_filter_c:'a``)

  val tactic_condition =
    ``surface_solver_x \/ ~surface_solver_x``
  val tactic_rwt =
    ASSUME
      (mk_imp
         (tactic_condition,
          mk_eq(``(surface_solver_f : bool -> 'b) surface_solver_x``,
                ``surface_solver_y:'b``)))
  val tactic_solver =
    mk_tactic_solver
      ("surface tactic solver",
       ACCEPT_TAC
         (SPEC ``surface_solver_x:bool`` boolTheory.EXCLUDED_MIDDLE))
  exception SURFACE_SOLVER_CONTEXT
  val tactic_rewr =
    Cond_rewrExt.COND_REWR_CONV_WITH_CONTEXT
      ("surface tactic rewrite",tactic_rwt) false
  val tactic_reducer =
    Traverse.CONTEXT_REDUCER
      {name=SOME "surface tactic reducer", initial=SURFACE_SOLVER_CONTEXT,
       addcontext=fn (ctxt,_) => ctxt,
       apply=fn {solver,stack,cond_depth,term_ord,...} =>
         tactic_rewr
           {solver=solver, stack=stack, cond_depth=cond_depth,
            term_ord=term_ord}}
  val tactic_solver_ss =
    pureSimps.pure_ss ++ dproc_ss tactic_reducer
    |> add_unsafe_solver tactic_solver

  val context_fact =
    SPEC ``surface_context_p:bool`` boolTheory.EXCLUDED_MIDDLE
  val context_tactic_solver =
    mk_tactic_solver ("surface context solver",FIRST_ASSUM ACCEPT_TAC)
  val context_result =
    #solve context_tactic_solver
      {stack=[],context_thms=[context_fact],recurse=fn tm => REFL tm}
      (concl context_fact)

  val _ = check "mk_tactic_solver discharges context theorem assumptions"
    (fn () => null (hyp context_result) andalso
              aconv (concl context_result) (concl context_fact))

  val _ = convtest
    ("mk_tactic_solver discharges a SIMP_CONV side condition",
     SIMP_CONV tactic_solver_ss [],
     ``(surface_solver_f : bool -> 'b) surface_solver_x``,
     ``surface_solver_y:'b``)

  (* The solver's tactic runs in the context given to the simplifier
     tactic, not in the ambient one. *)
  val marker_slot : bool Context.Data.slot =
    Context.Data.new {name = "native-extension.tactic-solver-context",
                      empty = false, pp = Bool.toString}
  val marked = Context.Data.put marker_slot true (Context.snapshot ())
  val marked_goal = ``surface_marked_p \/ ~surface_marked_p``
  fun marked_tac g ctxt =
    if Context.Data.get marker_slot ctxt then
      ACCEPT_TAC (SPEC ``surface_marked_p:bool`` EXCLUDED_MIDDLE) g ctxt
    else NO_TAC g ctxt
  val marked_ss =
    add_safe_solver (mk_tactic_solver ("marked solver",marked_tac))
      pureSimps.pure_ss
  val _ = check "mk_tactic_solver uses the simplifier tactic's context"
    (fn () => null (#1 (GEN_SIMP_TAC {safe=true} marked_ss []
                          ([],marked_goal) marked)))

  val _ = shouldfail
    {testfn=SIMP_CONV tactic_solver_ss
       [Excl "surface tactic reducer"],
     printresult=thm_to_string,
     printarg=term_to_string,
     checkexn=fn UNCHANGED => true | _ => false}
    ``(surface_solver_f : bool -> 'b) surface_solver_x``

  val depth_c1 = ``surface_depth_p1 = surface_depth_q1``
  val depth_c2 = ``surface_depth_p2 = surface_depth_q2``
  val depth_c3 = ``surface_depth_p3 = surface_depth_q3``
  val depth_c4 = ``surface_depth_p4 = surface_depth_q4``
  val depth_c5 = ``surface_depth_p5 = surface_depth_q5``
  fun cond_true condition lhs =
    ASSUME (mk_imp(condition,mk_eq(lhs,boolSyntax.T)))
  val depth_lhs = ``(surface_depth_f : 'a -> 'b) surface_depth_x``
  val depth_rhs = ``surface_depth_y:'b``
  val depth_rwts =
    [ASSUME (mk_imp(depth_c1,mk_eq(depth_lhs,depth_rhs))),
     cond_true depth_c2 depth_c1, cond_true depth_c3 depth_c2,
     cond_true depth_c4 depth_c3, cond_true depth_c5 depth_c4,
     ASSUME (mk_eq(depth_c5,boolSyntax.T))]

  val _ = convtest
    ("set_cond_depth configures a simpset invocation",
     SIMP_CONV (set_cond_depth 40 pureSimps.pure_ss) depth_rwts,
     depth_lhs, depth_rhs)

  val _ = convtest
    ("set_term_ord configures permutative rewriting per simpset",
     SIMP_CONV (set_term_ord reverse_order pureSimps.pure_ss)
               [boolTheory.EQ_SYM_EQ],
     ``surface_order_x:'a = surface_order_y``,
     ``surface_order_y:'a = surface_order_x``)

(* ---------------------------------------------------------------------- *)
(* Congruence theorems in simpset fragments.                               *)
(* ---------------------------------------------------------------------- *)

local
  val cond_base = pureSimps.pure_ss ++ boolSimps.BOOL_ss
  val cond_tm =
    ``if surface_cong_p then
        (surface_cong_f : bool -> 'a) surface_cong_p
      else surface_cong_g surface_cong_p``
  val cond_result =
    ``if surface_cong_p then
        (surface_cong_f : bool -> 'a) T
      else surface_cong_g F``
  val theorem_ss =
    cond_base ++
    SSFRAG
      {name=NONE, convs=[], rewrs=[], ac=[], filter=NONE, dprocs=[],
       congs=[boolTheory.COND_CONG]}
in
  val _ = convtest
    ("SSFRAG congs installs a COND congruence theorem",
     QCONV (SIMP_CONV theorem_ss []), cond_tm, cond_result)
end

(* ---------------------------------------------------------------------- *)
(* Tactic-layer solver and looper loop.                                    *)
(* ---------------------------------------------------------------------- *)

local
  fun tactic_result expected result =
    case result of
        Exn.Res (sgs,_) => list_eq goal_eq expected sgs
      | Exn.Exn _ => false
  fun run tac goal = Exn.capture (runtac (VALID tac)) goal
  fun inc r = r := !r + 1
  fun solver_failure name =
    raise mk_HOL_ERR "selftest" name "not applicable"

  val loop_p = ``loop_p:bool``
  val loop_q = ``loop_q:bool``
  val loop_r = ``loop_r:bool``
  val looper_calls = ref 0
  fun conjunction_looper _ g =
    (inc looper_calls; CONJ_TAC g)
  val solver_calls = ref 0
  fun loop_solver _ tm =
    (inc solver_calls;
     if aconv tm loop_p then ASSUME loop_p
     else solver_failure "loop_solver")
  val loop_ss =
    empty_ss
    |> add_looper ("selftest conjunction",conjunction_looper)
    |> add_unsafe_solver {name="selftest loop solver",solve=loop_solver}
  val loop_result =
    run (GEN_SIMP_TAC {safe=false} loop_ss [markerLib.NoAsms])
        ([loop_p],mk_conj(loop_p,loop_q))

  val _ = tprint "GEN_SIMP_TAC restarts after a looper on every subgoal"
  val _ =
    if tactic_result [([loop_p],loop_q)] loop_result andalso
       !solver_calls = 3 andalso !looper_calls = 2
    then OK()
    else die "looper restart or TRY termination failed"

  val safe_tm =
    ``safe_solver_p \/ ~safe_solver_p``
  val unsafe_tm =
    ``unsafe_solver_p \/ ~unsafe_solver_p``
  val safe_th = SPEC ``safe_solver_p:bool`` boolTheory.EXCLUDED_MIDDLE
  val unsafe_th =
    SPEC ``unsafe_solver_p:bool`` boolTheory.EXCLUDED_MIDDLE
  val safe_calls = ref 0
  val unsafe_calls = ref 0
  fun exact_solver calls th _ tm =
    (inc calls;
     if aconv tm (concl th) then th
     else solver_failure "exact_solver")
  val selection_ss =
    empty_ss
    |> add_safe_solver
         {name="selftest safe",solve=exact_solver safe_calls safe_th}
    |> add_unsafe_solver
         {name="selftest.unsafe.solver",
          solve=exact_solver unsafe_calls unsafe_th}

  val _ = tprint "GEN_SIMP_TAC safe mode selects only safe final solvers"
  val _ =
    if tactic_result []
         (run (GEN_SIMP_TAC {safe=true} selection_ss []) ([],safe_tm))
       andalso !safe_calls = 1 andalso !unsafe_calls = 0
    then OK()
    else die "safe mode selected the wrong final-solver list"

  val _ = tprint "GEN_SIMP_TAC unsafe mode selects only unsafe solvers"
  val _ =
    if tactic_result []
         (run (GEN_SIMP_TAC {safe=false} selection_ss []) ([],unsafe_tm))
       andalso !safe_calls = 1 andalso !unsafe_calls = 1
    then OK()
    else die "unsafe mode selected the wrong final-solver list"

  val _ = tprint "ExclX removes a named solver for one invocation"
  val _ =
    if tactic_result [([],unsafe_tm)]
         (run (GEN_SIMP_TAC {safe=false} selection_ss
                            [ExclX "selftest.unsafe.solver"])
              ([],unsafe_tm)) andalso
       !unsafe_calls = 1
    then OK()
    else die "ExclX did not remove the named solver"

  val context_p = ``final_context_p:bool``
  val context_q = ``final_context_q:bool``
  val context_imp = mk_imp(context_p,context_q)
  val context_calls = ref 0
  fun context_solver {context_thms,...} tm =
    let
      val _ = inc context_calls
      fun find conclusion =
        case List.find (aconv conclusion o concl) context_thms of
            SOME th => th
          | NONE => solver_failure "context_solver"
    in
      if aconv tm context_q then MP (find context_imp) (find context_p)
      else solver_failure "context_solver"
    end
  val context_ss =
    add_unsafe_solver
      {name="selftest final context",solve=context_solver} empty_ss
  val context_result =
    run (GEN_SIMP_TAC {safe=false} context_ss [])
        ([context_p,context_imp],context_q)

  val _ = tprint "final solver sees tactic-layer context theorems"
  val _ =
    if tactic_result [] context_result andalso !context_calls = 1
    then OK()
    else die "final solver could not prove the goal from assumptions"

  val global_p = ``global_context_x = global_context_x``
  val global_pth = REFL ``global_context_x:'a``
  val global_q = ``global_context_q \/ ~global_context_q``
  val global_qth =
    SPEC ``global_context_q:bool`` boolTheory.EXCLUDED_MIDDLE
  val global_impth = DISCH global_p (ADD_ASSUM global_p global_qth)
  val global_context_calls = ref 0
  fun global_context_solver {context_thms,...} tm =
    let
      val _ = inc global_context_calls
      fun find conclusion =
        case List.find (aconv conclusion o concl) context_thms of
            SOME th => th
          | NONE => solver_failure "global_context_solver"
    in
      if aconv tm global_q then MP (find (concl global_impth))
                                  (find global_p)
      else solver_failure "global_context_solver"
    end
  val global_context_ss =
    add_unsafe_solver
      {name="selftest global context",solve=global_context_solver} empty_ss
  val global_cfg =
    {droptrues=true,elimvars=false,strip=true,oldestfirst=true}
  val global_context_result =
    run (global_simp_tac global_cfg global_context_ss
                         [global_pth,global_impth])
        ([],global_q)

  val _ = tprint "global_simp_tac final solver sees supplied theorems"
  val _ =
    if tactic_result [] global_context_result andalso
       !global_context_calls = 1
    then OK()
    else die "global_simp_tac lost the final solver context"

  val entry_looper_ss =
    add_looper ("selftest.entry.conjunction",fn _ => CONJ_TAC) empty_ss
  val entry_goal = ([],mk_conj(loop_p,loop_q))
  val entry_subgoals = [([],loop_p),([],loop_q)]

  val _ = tprint "FULL_SIMP_TAC runs loopers in its final goal step"
  val _ =
    if tactic_result entry_subgoals
         (run (FULL_SIMP_TAC entry_looper_ss []) entry_goal)
    then OK()
    else die "FULL_SIMP_TAC did not use GEN_SIMP_TAC"

  val _ = tprint "global_simp_tac runs loopers in its final goal step"
  val _ =
    if tactic_result entry_subgoals
         (run (global_simp_tac global_cfg entry_looper_ss []) entry_goal)
    then OK()
    else die "global_simp_tac did not use GEN_SIMP_TAC"

  val _ = tprint "ExclX removes a named looper for one invocation"
  val _ =
    if tactic_result [entry_goal]
         (run (SIMP_TAC entry_looper_ss
                        [ExclX "selftest.entry.conjunction"])
              entry_goal)
    then OK()
    else die "ExclX did not remove the named looper"

  val split_named_user_ss =
    add_looper ("split user",fn _ => CONJ_TAC) empty_ss
  val _ = tprint "a user looper named split is resolved as a user looper"
  val _ =
    if tactic_result [entry_goal]
         (run (SIMP_TAC split_named_user_ss [ExclX "split user"])
              entry_goal)
    then OK()
    else die "the split namespace swallowed an ordinary looper"

  val shared_rwt =
    ASSUME ``(shared_rule_left:'a) = shared_rule_right``
  val shared_ss =
    empty_ss
    |> (fn ss =>
          ss ++ rewrites_with_names
            [({Thy="",Name="shared_identity"},shared_rwt)])
    |> add_looper ("shared_identity",fn _ => CONJ_TAC)
  val _ = convtest
    ("qualified looper exclusion leaves a same-named rewrite",
     SIMP_CONV shared_ss [ExclX "looper:shared_identity"],
     ``shared_rule_left:'a``, ``shared_rule_right:'a``)
  val _ = tprint "qualified rule exclusion leaves a same-named looper"
  val _ =
    if tactic_result entry_subgoals
         (run (SIMP_TAC shared_ss [ExclX "rule:shared_identity"])
              entry_goal)
    then OK()
    else die "qualified rule exclusion removed the looper"
  val _ = shouldfail
    {testfn=SIMP_CONV shared_ss [Excl "shared_identity"],
     printresult=thm_to_string,
     printarg=K "bare Excl prefers the rewrite over a same-named looper",
     checkexn=fn UNCHANGED => true | _ => false}
    ``shared_rule_left:'a``
  val _ = tprint "bare rule exclusion leaves a same-named looper"
  val _ =
    if tactic_result entry_subgoals
         (run (SIMP_TAC shared_ss [Excl "shared_identity"]) entry_goal)
    then OK()
    else die "bare rule exclusion removed the looper"
  (* Exclusion requests retain their argument order: once the rule is
     gone, the extended bare name resolves to the looper instead. *)
  val _ = tprint "mixed literal/extended exclusions resolve in order"
  val _ =
    if tactic_result [entry_goal]
         (run (SIMP_TAC shared_ss
           [Excl "shared_identity", ExclX "shared_identity"]) entry_goal)
       andalso tactic_result entry_subgoals
         (run (SIMP_TAC shared_ss
           [ExclX "shared_identity", Excl "shared_identity"]) entry_goal)
    then OK () else die "mixed exclusion order was lost"
  val _ = tprint "adjacent extended exclusions see pending rule deletions"
  val _ =
    if tactic_result [entry_goal]
         (run (SIMP_TAC shared_ss
           [ExclX "rule:shared_identity", ExclX "shared_identity"])
           entry_goal)
    then OK () else die "extended resolution ignored pending exclusions"
  val ambiguous_ss =
    empty_ss
    |> add_looper ("shared_strategy",fn _ => CONJ_TAC)
    |> add_unsafe_solver
         {name="shared_strategy",solve=fn _ => fn _ =>
            solver_failure "shared_strategy"}
  val _ = shouldfail
    {testfn=fn () =>
       runtac (VALID (SIMP_TAC ambiguous_ss [ExclX "shared_strategy"]))
              entry_goal,
     printresult=K "unexpected success", printarg=K "ambiguous ExclX",
     checkexn=fn HOL_ERR error =>
       String.isSubstring "ambiguous" (Feedback.message_of error)
       | _ => false} ()

  val _ = tprint "literal Excl never falls back to strategy targets"
  val _ =
    if tactic_result entry_subgoals
         (run (SIMP_TAC ambiguous_ss [Excl "shared_strategy"]) entry_goal)
       andalso tactic_result entry_subgoals
         (run (SIMP_TAC entry_looper_ss
           [Excl "selftest.entry.conjunction"]) entry_goal)
       andalso tactic_result []
         (run (GEN_SIMP_TAC {safe=false} selection_ss
           [Excl "selftest.unsafe.solver"]) ([],unsafe_tm))
    then OK () else die "literal Excl selected a strategy namespace"

  (* Only the simpset's entries contest a name: bool.CONJ_COMM exists but
     is no rule of this simpset, so the looper is the sole target. *)
  val theorem_named_looper_ss =
    add_looper ("CONJ_COMM",fn _ => CONJ_TAC) empty_ss
  val _ = tprint "a looper named like an uninstalled theorem is excludable"
  val _ =
    if tactic_result [entry_goal]
         (run (SIMP_TAC theorem_named_looper_ss [ExclX "CONJ_COMM"])
              entry_goal)
    then OK()
    else die "an uninstalled theorem made the looper's name ambiguous"

  (* An unqualified Excl that matches nothing in the simpset is a silent
     no-op, as in simpLib.  Only the simpset decides: a theorem that exists
     but is not installed is as much a no-op as a name that denotes
     nothing. ExclX explicitly selects a target, so matching nothing there
     aborts. *)
  val excl_true_t = ``T /\ (selftest_catalogue_p:bool)``
  val excl_warnings = ref ([] : string list)
  val excl_outstream = !Feedback.WARNING_outstream
  val _ = Feedback.WARNING_outstream :=
            (fn s => excl_warnings := s :: !excl_warnings)
  fun excl_warned name =
    List.exists (String.isSubstring name) (!excl_warnings)
    before excl_warnings := []
  val _ = convtest
    ("unmatched unqualified Excl leaves the simpset alone",
     SIMP_CONV bool_ss [Excl "definitely_not_a_theorem"],
     excl_true_t, ``selftest_catalogue_p:bool``)
  val unmatched_warned = excl_warned "definitely_not_a_theorem"
  val _ = convtest
    ("Excl of a theorem the simpset does not hold leaves it alone",
     SIMP_CONV bool_ss [Excl "CONJ_COMM"],
     excl_true_t, ``selftest_catalogue_p:bool``)
  val uninstalled_warned = excl_warned "CONJ_COMM"
  val _ = convtest
    ("bare kernel-spelled Excl is a no-op, as in simpLib",
     SIMP_CONV bool_ss [Excl "bool$AND_CLAUSES"],
     excl_true_t, ``selftest_catalogue_p:bool``)
  val bare_kernel_warned = excl_warned "bool$AND_CLAUSES"
  val _ = convtest
    ("-* leaves the kernel spelling uninterpreted, as in simpLib",
     SIMP_CONV (bool_ss -* ["bool$AND_CLAUSES"]) [],
     excl_true_t, ``selftest_catalogue_p:bool``)
  val _ = shouldfail
    {testfn=SIMP_CONV bool_ss [ExclX "rule:bool$AND_CLAUSES"],
     printresult=thm_to_string,
     printarg=K "rule: ExclX takes the kernel Thy$Name spelling",
     checkexn=fn UNCHANGED => true | _ => false}
    excl_true_t
  val kernel_name_matched = null (!excl_warnings)
  val _ = Feedback.WARNING_outstream := excl_outstream

  val _ = tprint "unmatched unqualified Excl is silent"
  val _ =
    if unmatched_warned then die "unmatched unqualified Excl warned"
    else OK()

  val _ = tprint "Excl of a theorem the simpset does not hold is silent"
  val _ =
    if uninstalled_warned then die "Excl of an uninstalled theorem warned"
    else OK()

  val _ = tprint "bare kernel-spelled Excl is silent"
  val _ =
    if bare_kernel_warned then die "bare Thy$Name Excl warned"
    else OK()

  val _ = tprint "a kernel-spelled rule: ExclX resolves to its theorem"
  val _ =
    if kernel_name_matched then OK()
    else die "Thy$Name rule: ExclX was treated as matching nothing"

  val _ = shouldfail
    {testfn=fn () =>
       SIMP_CONV empty_ss [ExclX "rule:definitely_not_a_theorem"]
         ``selftest_catalogue_p:bool``,
     printresult=thm_to_string,
     printarg=K "unknown namespaced theorem exclusion",
     checkexn=fn HOL_ERR error =>
       String.isSubstring "did not match" (Feedback.message_of error)
       | _ => false} ()

  (* A simpset entry keeps whatever theory its rewrite was named with, and
     nothing requires that theory to be an ancestor of the one being
     built.  The rule: namespace reaches such an entry by its qualified
     name in either spelling.  Bare Excl retains simpLib's strict parser. *)
  val unloaded_thy = "no_such_ancestor_selftest"
  val unloaded_rwt =
    ASSUME ``(unloaded_rule_left:'a) = unloaded_rule_right``
  val unloaded_lhs = ``unloaded_rule_left:'a``
  val unloaded_rhs = ``unloaded_rule_right:'a``
  val unloaded_ss =
    empty_ss ++ rewrites_with_names
      [({Thy=unloaded_thy,Name="unloaded_identity"},unloaded_rwt)]
  val _ = convtest
    ("a rewrite named in an unloaded theory is installed",
     SIMP_CONV unloaded_ss [], unloaded_lhs, unloaded_rhs)
  fun unloaded_excluded (description,name) =
    shouldfail
      {testfn=SIMP_CONV unloaded_ss [ExclX name],
       printresult=thm_to_string,
       printarg=K description,
       checkexn=fn UNCHANGED => true | _ => false}
      unloaded_lhs
  val _ =
    unloaded_excluded
      ("Thy.Name rule: ExclX of a rewrite from an unloaded theory",
       "rule:" ^ unloaded_thy ^ ".unloaded_identity")
  val _ =
    unloaded_excluded
      ("Thy$Name rule: ExclX of a rewrite from an unloaded theory",
       "rule:" ^ unloaded_thy ^ "$unloaded_identity")

  val _ = shouldfail
    {testfn=fn () =>
       SIMP_CONV unloaded_ss [Excl (unloaded_thy ^ ".unloaded_identity")]
         unloaded_lhs,
     printresult=thm_to_string,
     printarg=K "bare dotted Excl rejects a non-ancestor, as in simpLib",
     checkexn=fn HOL_ERR error =>
       String.isSubstring "bad theory name" (Feedback.message_of error)
       | _ => false} ()
  val dotted_looper_ss =
    add_looper (unloaded_thy ^ ".looper",fn _ => CONJ_TAC) empty_ss
  val _ = shouldfail
    {testfn=fn () =>
       runtac (VALID
         (SIMP_TAC dotted_looper_ss [Excl (unloaded_thy ^ ".looper")]))
         entry_goal,
     printresult=K "unexpected success",
     printarg=K "bare Excl cannot bypass the strict parser for a looper",
     checkexn=fn HOL_ERR error =>
       String.isSubstring "bad theory name" (Feedback.message_of error)
       | _ => false} ()

  (* [-*] is published with the stricter reading and keeps it. *)
  val _ = shouldfail
    {testfn=fn () => empty_ss -* [unloaded_thy ^ ".unloaded_identity"],
     printresult=K "unexpected success",
     printarg=K "-* on a name from an unloaded theory",
     checkexn=fn HOL_ERR error =>
       String.isSubstring "bad theory name" (Feedback.message_of error)
       | _ => false} ()

  (* An unmatched bare Excl still records a deletion.  Removing a filter
     recompiles surviving fragments, but must not revive the deleted rule.
     These constructions use only simpLib's public API. *)
  val history_filter =
    SSFRAG
      {name=SOME "exclusion history filter", convs=[], rewrs=[], ac=[],
       filter=SOME (fn _ => []), dprocs=[], congs=[]}
  val history_lhs = ``history_filtered_a:bool``
  val history_rule = ASSUME ``history_filtered_a:bool = T``
  val history_filtered =
    mk_simpset
      [history_filter,
       name_ss "exclusion history rewrite"
         (rewrites_with_names [({Thy="",Name="history_r"},history_rule)])]
  val _ = convtest
    ("removing a rewrite filter revives an undeleted rule",
     SIMP_CONV
       (remove_ssfrags ["exclusion history filter"] history_filtered) [],
     history_lhs, ``T``)
  val history_excluded = history_filtered && [Excl "history_r"]
  val _ = convtest
    ("unmatched bare Excl survives filter-removal replay",
     QCONV (SIMP_CONV
       (remove_ssfrags ["exclusion history filter"] history_excluded) []),
     history_lhs, history_lhs)
  val _ = convtest
    ("unmatched bare Excl survives filter-exclusion replay",
     QCONV (SIMP_CONV
       (exclude_ssfrags ["exclusion history filter"] history_excluded) []),
     history_lhs, history_lhs)
  val _ = convtest
    ("unmatched -* survives filter-removal replay",
     QCONV (SIMP_CONV
       (remove_ssfrags ["exclusion history filter"]
          (history_filtered -* ["history_r"])) []),
     history_lhs, history_lhs)

  (* Strict history reparses under the current theory ancestry, just as
     simpLib's DELETE_EVENT does.  Link a temporary ancestor without
     exporting a theory, then restore the context before replaying. *)
  val _ = let
    val saved = Context.snapshot ()
    fun run () = let
      val replay_thy = "strictExclusionReplayFixture"
      val _ = Theory.link_parents (replay_thy,"selftest") []
      val dummy = "strict exclusion replay dummy"
      val replay_ss =
        mk_simpset
          [name_ss dummy empty_ssfrag,
           rewrites_with_names
             [({Thy=replay_thy,Name="history_r"},history_rule)]]
      val qualified = replay_thy ^ ".history_r"
      val strict_deleted = replay_ss -* [qualified]
      val strict_bare = replay_ss && [Excl qualified]
      val relaxed_deleted = replay_ss && [ExclX ("rule:" ^ qualified)]
      val resolved_bare = replay_ss && [ExclX qualified]
      val mixed = replay_ss &&
        [Excl "unmatched_history_batch",ExclX ("rule:" ^ qualified),
         Excl qualified,Excl "unmatched_history_batch"]
      val present = Context.snapshot ()
      val _ = Context.restore saved
      fun strict_replay (description,ss) =
        shouldfail
          {testfn=remove_ssfrags [dummy], printresult=K "unexpected success",
           printarg=K description,
           checkexn=fn HOL_ERR error =>
             String.isSubstring "bad theory name" (Feedback.message_of error)
             | _ => false} ss
      val _ = strict_replay
        ("-* history reparses names after Context.restore",strict_deleted)
      val _ = strict_replay
        ("bare Excl history reparses names after Context.restore",strict_bare)
      val _ = strict_replay
        ("mixed strict/resolved batch reparses only strict names",mixed)
      val _ = convtest
        ("rule: history retains its parsed pattern after Context.restore",
         QCONV (SIMP_CONV (remove_ssfrags [dummy] relaxed_deleted) []),
         history_lhs, history_lhs)
      val _ = convtest
        ("bare ExclX history retains its resolved rule after Context.restore",
         QCONV (SIMP_CONV (remove_ssfrags [dummy] resolved_bare) []),
         history_lhs, history_lhs)
      val _ = Context.restore present
      val _ = convtest
        ("mixed batch replays after restoring the naming context",
         QCONV (SIMP_CONV (remove_ssfrags [dummy] mixed) []),
         history_lhs, history_lhs)
    in () end
  in Portable.finally (fn () => Context.restore saved) run () end

  (* A relaxed rule: exclusion is recorded with its resolved pattern, so
     rebuilding does not ask again what that name means. *)
  val unloaded_after_excl =
    unloaded_ss && [ExclX ("rule:" ^ unloaded_thy ^ ".unloaded_identity")]
  val unloaded_replayed =
    exclude_ssfrags ["no_such_fragment_selftest"] unloaded_after_excl
  val _ = shouldfail
    {testfn=SIMP_CONV unloaded_replayed [],
     printresult=thm_to_string,
     printarg=K "simpset rebuilt over a recorded qualified exclusion",
     checkexn=fn UNCHANGED => true | _ => false}
    unloaded_lhs

  (* An ancestor-qualified bare name matching nothing is a silent no-op. *)
  val unloaded_warnings = ref ([] : string list)
  val unloaded_outstream = !Feedback.WARNING_outstream
  val _ = Feedback.WARNING_outstream :=
            (fn s => unloaded_warnings := s :: !unloaded_warnings)
  val _ = convtest
    ("unmatched qualified Excl leaves the simpset alone",
     SIMP_CONV unloaded_ss [Excl "bool.definitely_not_a_rule"],
     unloaded_lhs, unloaded_rhs)
  val unloaded_typo_warned =
    List.exists (String.isSubstring "definitely_not_a_rule")
                (!unloaded_warnings)
  val _ = Feedback.WARNING_outstream := unloaded_outstream
  val _ = tprint "unmatched qualified Excl is silent"
  val _ =
    if unloaded_typo_warned then die "unmatched qualified Excl warned"
    else OK()

  val bounded_calls = ref 0
  fun bounded_conjunction_looper _ g =
    (inc bounded_calls; CONJ_TAC g)
  val bounded_ss =
    empty_ss
    |> add_looper ("selftest bounded conjunction",
                   bounded_conjunction_looper)
    |> limit 1
  val bounded_goal = mk_conj(loop_p,mk_conj(loop_q,loop_r))
  val bounded_result =
    run (GEN_SIMP_TAC {safe=false} bounded_ss [markerLib.NoAsms])
        ([],bounded_goal)

  val _ = tprint "simpset limit bounds successful looper rounds"
  val _ =
    if tactic_result [([],loop_p),([],mk_conj(loop_q,loop_r))]
                     bounded_result andalso
       !bounded_calls = 1
    then OK()
    else die "looper ignored the simpset round limit"

  fun legacy_asm_simp_tac ss ths =
    markerLib.process_taclist_then {arg=ths}
      (CONV_TAC o SIMP_CONV ss)
  fun theorem_eq th1 th2 =
    aconv (concl th1) (concl th2) andalso
    list_eq aconv (hyp th1) (hyp th2)
  fun compare_tactics tac1 tac2 goal =
    let
      val (sgs1,vf1) = runtac tac1 goal
      val (sgs2,vf2) = runtac tac2 goal
      val same_goals = list_eq goal_eq sgs1 sgs2
      val th1 = vf1 (map mk_thm sgs1)
      val th2 = vf2 (map mk_thm sgs2)
    in
      same_goals andalso theorem_eq th1 th2
    end
  val zero_goal =
    ([``zero_x = F``],``zero_pred (zero_x:bool):bool``)

  val _ = tprint "empty hooks preserve legacy ASM_SIMP_TAC theorems"
  val _ =
    if compare_tactics
         (legacy_asm_simp_tac bool_ss [])
         (ASM_SIMP_TAC bool_ss []) zero_goal
    then OK()
    else die "ASM_SIMP_TAC changed with empty strategy hooks"

  val _ = tprint "empty hooks preserve legacy SIMP_TAC theorems"
  val _ =
    if compare_tactics
         (legacy_asm_simp_tac bool_ss [markerLib.NoAsms])
         (SIMP_TAC bool_ss []) zero_goal
    then OK()
    else die "SIMP_TAC changed with empty strategy hooks"
in
end

(* ---------------------------------------------------------------------- *)
(* Splitter core: conclusion and assumption splits.                       *)

val mk_asm_split = splitLib.mk_asm_split

val _ = let
  val if_split = TypeBase.case_pred_imp_of ``:bool``
  val if_asm_split =
    mk_asm_split (TypeBase.case_pred_disj_of ``:bool``)
  val split_parameter = ``split_parameter:bool``
  val parameterised_if_asm_split =
    TypeBase.case_pred_disj_of ``:bool``
      |> GEN split_parameter
      |> mk_asm_split
  val expected_parameterised_if_asm_split = GEN split_parameter if_asm_split

  val _ = tprint "splitter: predicate need not be the first quantifier"
  val _ =
    if aconv (concl parameterised_if_asm_split)
             (concl expected_parameterised_if_asm_split)
    then OK()
    else die "mk_asm_split specialised the wrong quantified variable"

  val _ = convtest
    ("splitter: conditional",
     SPLIT_CONV [if_split],
     ``P (if b then x:'a else y) : bool``,
     ``(b ==> P (x:'a)) /\ (~b ==> P y)``)

  val _ = convtest
    ("splitter: conditional under a referenced forall binder",
     SPLIT_CONV [if_split],
     ``!z:'a. P z (if Q z then x:'b else y)``,
     ``!z:'a. (Q z ==> P z (x:'b)) /\ (~Q z ==> P z y)``)

  val _ = convtest
    ("splitter: unreferenced binder remains in the context",
     SPLIT_CONV [if_split],
     ``!z:'a. P (if b then x:'b else y) z``,
     ``(b ==> !z:'a. P (x:'b) z) /\
       (~b ==> !z:'a. P (y:'b) z)``)

  val _ = convtest
    ("splitter: all alpha-equivalent occurrences are replaced",
     SPLIT_CONV [if_split],
     ``P (if b then (\z:'a. z) else f) /\
       Q (if b then (\w:'a. w) else f)``,
     ``(b ==> P (\z:'a. z) /\ Q (\w:'a. w)) /\
       (~b ==> P f /\ Q f)``)

  val _ = convtest
    ("splitter: outermost pack is selected first",
     SPLIT_CONV [if_split],
     ``P (if (if b then c else d) then x:'a else y) : bool``,
     ``((if b then c else d) ==> P (x:'a)) /\
       (~(if b then c else d) ==> P y)``)

  val _ = convtest
    ("splitter: one split per conversion invocation",
     SPLIT_CONV [if_split],
     ``P (if b then x:'a else y) /\ Q (if c then u else v)``,
     ``(b ==> P (x:'a) /\ Q (if c then u else v)) /\
       (~b ==> P y /\ Q (if c then u else v))``)

  val (if_vars, if_eq) = strip_forall (concl if_split)
  val reflexive_split = GENL if_vars (REFL (lhs if_eq))
  val _ = convtest
    ("splitter: later rule wins a tie at the same occurrence",
     SPLIT_CONV [if_split, reflexive_split],
     ``P (if b then x:'a else y) : bool``,
     ``P (if b then x:'a else y) : bool``)

  val generic_k_split =
    GEN_ALL (REFL ``P (K (x:'a) (y:'b)) : bool``)
  val bool_k_split =
    INST_TYPE [alpha |-> bool, beta |-> bool] generic_k_split
  val _ = convtest
    ("splitter: distinct constant type shapes are not merged",
     SPLIT_CONV [bool_k_split, generic_k_split],
     ``P (K T (f:bool -> bool)) : bool``,
     ``P (K T (f:bool -> bool)) : bool``)

  val rejected_k_split =
    GEN_ALL (REFL ``p (K (x:bool) (p:bool -> bool))``)
  val _ = convtest
    ("splitter: rejection resumes search in later subtrees",
     SPLIT_CONV [if_split, rejected_k_split],
     ``R (K (x:bool) (p:bool -> bool)) /\ Q (if b then u:bool else v)``,
     ``(b ==> R (K (x:bool) (p:bool -> bool)) /\ Q (u:bool)) /\
       (~b ==> R (K x p) /\ Q (v:bool))``)

  val _ = shouldfail
    {testfn=fn () => SPLIT_CONV [REFL ``P (if b then x else y)``],
     printresult=K "unexpected conversion",
     printarg=K "splitter rejects a rule with a free context variable",
     checkexn=fn HOL_ERR _ => true | _ => false} ()

  val _ = shouldfail
    {testfn=fn () => SPLIT_CONV [boolTheory.TRUTH],
     printresult=K "unexpected conversion",
     printarg=K "splitter rejects a non-equational rule",
     checkexn=fn HOL_ERR _ => true | _ => false} ()

  val _ = shouldfail
    {testfn=SPLIT_CONV [if_split],
     printresult=thm_to_string,
     printarg=K "splitter rejects a partial case application",
     checkexn=fn HOL_ERR _ => true | _ => false}
    ``P (COND b) : bool``

  val _ = shouldfail
    {testfn=SPLIT_CONV [if_split],
     printresult=thm_to_string,
     printarg=K "splitter enforces the binder-body type test",
     checkexn=fn HOL_ERR _ => true | _ => false}
    ``P (\z:'a. if Q z then x:'b else y) : bool``

  val tactic_goal =
    ([], ``P (if b then x:'a else y) : bool``)
  val tactic_result =
    ``(b ==> P (x:'a)) /\ (~b ==> P y)``
  val _ = tprint "splitter: SPLIT_TAC performs one conclusion split"
  val _ =
    case valid (SPLIT_TAC [if_split]) tactic_goal of
        [([], result)] =>
          if aconv result tactic_result then OK()
          else die "SPLIT_TAC produced the wrong conclusion"
      | _ => die "SPLIT_TAC produced the wrong subgoals"

  fun has asm asms = List.exists (aconv asm) asms
  val asm_goal =
    ([``R (if b then x:'a else y) : bool``], ``G:bool``)
  val _ =
    tprint "splitter: conditional assumption split has clean cases"
  val _ =
    case valid (SPLIT_ASM_TAC [if_split, if_asm_split]) asm_goal of
        [(left, left_concl), (right, right_concl)] =>
          if aconv left_concl ``G:bool`` andalso
             aconv right_concl ``G:bool`` andalso
             has ``b:bool`` left andalso
             has ``R (x:'a) : bool`` left andalso
             has ``~b`` right andalso
             has ``R (y:'a) : bool`` right andalso
             not (goal_has_double_neg (left, left_concl)) andalso
             not (goal_has_double_neg (right, right_concl))
          then OK()
          else die "SPLIT_ASM_TAC produced incorrect conditional cases"
      | _ => die "SPLIT_ASM_TAC produced the wrong number of cases"

  val _ = tprint "splitter: assumption-only SPLIT_TAC leaves goal intact"
  val _ =
    case valid (SPLIT_TAC [if_asm_split]) asm_goal of
        [(_, left_concl), (_, right_concl)] =>
          if aconv left_concl (snd asm_goal) andalso
             aconv right_concl (snd asm_goal)
          then OK()
          else die "assumption-only SPLIT_TAC changed the conclusion"
      | _ => die "assumption-only SPLIT_TAC did not split the assumption"

  val _ = shouldfail
    {testfn=fn () => ignore (SPLIT_CONV [if_asm_split, TRUTH]),
     printresult=K "unexpected conversion construction",
     printarg=K "splitter: validates all rules before returning a conversion",
     checkexn=fn HOL_ERR _ => true | _ => false}
    ()

  val double_neg_goal =
    ([``~~R (if b then x:'a else y) : bool``], ``G:bool``)
  val _ =
    tprint "splitter: cleanup preserves a doubly negated assumption lhs"
  val _ =
    case valid (SPLIT_ASM_TAC [if_asm_split]) double_neg_goal of
        [left, right] =>
          if not (goal_has_double_neg left) andalso
             not (goal_has_double_neg right)
          then OK()
          else die "SPLIT_ASM_TAC retained a double negation"
      | _ => die "doubly negated assumption produced the wrong cases"

  val order_goal =
    ([``R (if b then x:'a else y) : bool``],
     ``Q (if c then u:'b else v) : bool``)
  val order_result =
    ``(c ==> Q (u:'b)) /\ (~c ==> Q v)``
  val _ = tprint "splitter: SPLIT_TAC prefers conclusion rules"
  val _ =
    case valid (SPLIT_TAC [if_asm_split, if_split]) order_goal of
        [(asms, result)] =>
          if aconv result order_result andalso
             has ``R (if b then x:'a else y) : bool`` asms
          then OK()
          else die "SPLIT_TAC did not prefer the conclusion"
      | _ => die "SPLIT_TAC split an assumption before the conclusion"

  val _ = shouldfail
    {testfn=valid (SPLIT_ASM_TAC [if_split]),
     printresult=K "unexpected tactic result",
     printarg=K "splitter: rhs shape routes conclusion rules away from asms",
     checkexn=fn HOL_ERR _ => true | _ => false}
    asm_goal

  (* The first assumption names COND but applies it to one argument, so
     no rule reaches it.  Naming a key is not splitting, so the splitter
     has to carry on to the assumption that does split. *)
  val partial_cond_asm = ``COND b = (f:'a -> 'a -> 'a)``
  val later_asm_goal =
    ([partial_cond_asm, ``R (if b then x:'a else y) : bool``],
     ``G:bool``)
  val _ =
    tprint "splitter: a later assumption is split when the first cannot"
  val _ =
    case valid (SPLIT_ASM_TAC [if_asm_split]) later_asm_goal of
        [(left, left_concl), (right, right_concl)] =>
          if aconv left_concl ``G:bool`` andalso
             aconv right_concl ``G:bool`` andalso
             has ``b:bool`` left andalso
             has ``R (x:'a) : bool`` left andalso
             has partial_cond_asm left andalso
             has ``~b`` right andalso
             has ``R (y:'a) : bool`` right andalso
             has partial_cond_asm right
          then OK()
          else die "SPLIT_ASM_TAC split the wrong assumption"
      | _ => die "SPLIT_ASM_TAC did not reach the later assumption"

  val _ = shouldfail
    {testfn=valid (SPLIT_ASM_TAC [if_asm_split]),
     printresult=K "unexpected tactic result",
     printarg=K "splitter: naming a key does not make an assumption split",
     checkexn=fn HOL_ERR _ => true | _ => false}
    ([partial_cond_asm], ``G:bool``)

  val _ = shouldfail
    {testfn=valid (SPLIT_TAC [if_split, if_asm_split]),
     printresult=K "unexpected tactic result",
     printarg=K "splitter: SPLIT_TAC fails when nothing splits",
     checkexn=fn HOL_ERR _ => true | _ => false}
    ([], ``R (z:'a) : bool``)
in
end

(* ---------------------------------------------------------------------- *)
(* Splitter integration: registration, caching, fragment, and rule APIs.  *)

val _ = let
  val if_split = type_split_of ``:bool``
  val if_split_again = type_split_of ``:bool``
  val if_asm_split = type_asm_split_of ``:bool``
  val if_asm_split_again = type_asm_split_of ``:bool``
  val named_if_split =
    Feedback.quiet_messages save_thm
      ("simp_split_selftest_rule", if_split)
  val named_if_asm_split =
    Feedback.quiet_messages save_thm
      ("simp_split_selftest_asm_rule",
       mk_asm_split (TypeBase.case_pred_disj_of ``:bool``))

  val _ = tprint "split settype and attribute start unclaimed"
  val _ =
    if not (List.exists (equal "split") (ThmSetData.all_set_types ())) andalso
       not (ThmAttribute.is_attribute "split") andalso null (split_thms ())
    then OK ()
    else die "ordinary loading claimed split registration"

  val _ = enable_split_attribute ()
  val _ = tprint "explicit split attribute has private storage and no generic set"
  val _ =
    if not (List.exists (equal "split") (ThmSetData.all_set_types ())) andalso
       ThmAttribute.is_attribute "split"
    then OK()
    else die "split registration is absent"

  val _ = tprint "datatype split cache returns the same rules twice"
  val _ =
    if aconv (concl if_split) (concl if_split_again) andalso
       aconv (concl if_asm_split) (concl if_asm_split_again)
    then OK()
    else die "cached datatype splits changed"

  val _ = tprint "datatype assumption split rule splits an assumption"
  val _ =
    case valid (SPLIT_ASM_TAC [if_asm_split])
           ([``R (if b then x:'a else y) : bool``], ``G:bool``) of
        [_, _] => OK()
      | _ => die "type_asm_split_of gave no assumption split"

  val context = Context.snapshot ()
  val bool_info = valOf (TypeBase.fetch ``:bool``)
  val nchotomy = TypeBasePure.nchotomy_of bool_info
  val fresh_nchotomy = EQ_MP (REFL (concl nchotomy)) nchotomy
  val fresh_info = TypeBasePure.put_nchotomy fresh_nchotomy bool_info
  val _ = TypeBase.write [fresh_info]
  val updated_if_split = type_split_of ``:bool``
  val _ = Context.restore context
  val restored_if_split = type_split_of ``:bool``
  val _ = tprint "datatype split cache tracks TypeBase replacements"
  val _ =
    if not (Portable.pointer_eq (if_split, updated_if_split)) andalso
       not (Portable.pointer_eq (updated_if_split, restored_if_split))
    then OK()
    else die "datatype split cache retained stale TypeBase rules"

  val split_goal =
    ([], ``P (if b then x:'a else y) : bool``)
  val split_result =
    ``(b ==> P (x:'a)) /\ (~b ==> P y)``
  val _ = tprint "split_ss splits a conditional in the conclusion"
  val _ =
    case valid (SIMP_TAC (bool_ss ++ split_ss) []) split_goal of
        [([], result)] =>
          if not (aconv result (#2 split_goal)) andalso
             not (can (find_term is_cond) result)
          then OK()
          else die "split_ss did not eliminate the conditional"
      | _ => die "split_ss produced the wrong conditional subgoals"

  val typebase_asm_goal =
    ([``P (if b then x:'a else y) : bool``], ``G:bool``)
  fun clean_asm_goal (asms, goal) =
    not (List.exists (can (find_term is_cond)) (goal :: asms)) andalso
    not (goal_has_double_neg (asms, goal))
  val _ = tprint "split_ss uses TypeBase splits in assumptions"
  val _ =
    case valid (SIMP_TAC (bool_ss ++ split_ss) []) typebase_asm_goal of
        [goal1, goal2] =>
          if List.all clean_asm_goal [goal1, goal2] then OK()
          else die "TypeBase assumption split retained conditional syntax"
      | _ => die "TypeBase assumption split produced the wrong subgoals"

  val _ = convtest
    ("split_ss cases_simp collapses a trivial split",
     SIMP_CONV (empty_ss ++ split_ss) [],
     ``(b ==> t) /\ (~b ==> t)``,
     ``t:bool``)

  val with_split = add_split named_if_split bool_ss
  val without_split =
    del_split (Theory.current_theory () ^ "$simp_split_selftest_rule")
      with_split
  val _ = tprint "add_split installs a conclusion looper by theorem name"
  val _ =
    case valid (SIMP_TAC with_split []) split_goal of
        [([], result)] =>
          if aconv result split_result then OK()
          else die "add_split installed the wrong looper"
      | _ => die "add_split produced the wrong subgoals"

  val _ = tprint "del_split removes a conclusion looper by theorem name"
  val _ =
    case valid (SIMP_TAC without_split []) split_goal of
        [([], result)] =>
          if aconv result (#2 split_goal) then OK()
          else die "del_split left the conclusion looper active"
      | _ => die "del_split produced the wrong subgoals"

  val _ = tprint "Split installs a split for one invocation"
  val _ =
    case valid (SIMP_TAC bool_ss [Split named_if_split]) split_goal of
        [([], result)] =>
          if not (aconv result (#2 split_goal)) andalso
             not (can (find_term is_cond) result)
          then OK()
          else die "Split did not install its per-invocation rule"
      | _ => die "Split produced the wrong subgoals"

  val split_name =
    "split " ^ Theory.current_theory () ^ "$simp_split_selftest_rule"
  val _ = tprint "ExclX suppresses a named split looper"
  val _ =
    case valid (SIMP_TAC with_split [ExclX split_name]) split_goal of
        [([], result)] =>
          if aconv result (#2 split_goal) then OK()
          else die "ExclX left the named split looper active"
      | _ => die "named split exclusion produced the wrong subgoals"

  val _ = tprint "ExclX split: suppresses a named split looper"
  val _ =
    case valid (SIMP_TAC with_split
      [ExclX ("split:" ^ Theory.current_theory () ^
              "$simp_split_selftest_rule")]) split_goal of
        [([],result)] =>
          if aconv result (#2 split_goal) then OK ()
          else die "namespaced split exclusion left its looper active"
      | _ => die "namespaced split exclusion produced wrong subgoals"

  val _ = tprint "ExclX case: suppresses TypeBase splits"
  val _ =
    case valid (SIMP_TAC (bool_ss ++ split_ss)
                 [ExclX "case:bool"]) split_goal of
        [([], result)] =>
          if aconv result (#2 split_goal) then OK()
          else die "split.case exclusion left the TypeBase split active"
      | _ => die "TypeBase split exclusion produced the wrong subgoals"

  (* Split/case exclusions must survive every history rebuild, including
     when the excluded target comes from a restored ambient store rather
     than a local looper. Keep the temporary registrations context-local. *)
  val _ = let
    val saved = Context.snapshot ()
    fun run () = let
      val thy = Theory.current_theory ()
      val key = thy ^ "$simp_split_selftest_rule"
      val asm_key = thy ^ "$simp_split_selftest_asm_rule"
      val dummy = "split exclusion replay dummy"
      val disposable = ASSUME ``replay_disposable:bool = T``
      val base = bool_ss ++ name_ss dummy (rewrites [disposable])
      fun check_goal label ss goal =
        (tprint label;
         case valid (SIMP_TAC ss []) goal of
             [(asms,result)] =>
               if aconv result (#2 goal) andalso
                  ListPair.allEq (uncurry aconv) (asms,#1 goal)
               then OK () else die "excluded splitter was re-enabled"
           | _ => die "excluded splitter changed the subgoals")
      fun check label ss = check_goal label ss split_goal
      fun replay_checks label ss =
        (check (label ^ ": direct") ss;
         check (label ^ ": remove fragment")
           (remove_ssfrags [dummy] ss);
         check (label ^ ": exclude fragment")
           (exclude_ssfrags [dummy] ss);
         check (label ^ ": filter rewrites")
           (filter_rewrites (fn (_,th) =>
              not (aconv (concl th) (concl disposable))) ss))
      val case_deleted = (base ++ split_ss) && [ExclX "case:bool"]
      val _ = replay_checks "case exclusion history" case_deleted
      val case_before = (base && [ExclX "case:bool"]) ++ split_ss
      val _ = replay_checks "case exclusion before fragment" case_before
      val case_twice = case_deleted && [ExclX "case:bool"]
      val _ = replay_checks "repeated case exclusion history" case_twice
      val local_deleted = add_split named_if_split base &&
        [ExclX ("split:" ^ key)]
      val local_readded = add_split named_if_split local_deleted
      val _ = replay_checks "split exclusion before re-add" local_readded
      val _ = replay_checks "split exclusion around fragment add"
        (add_split named_if_split
          (local_deleted ++ name_ss "split replay addition" empty_ssfrag))
      val _ = replay_checks "split exclusion after add"
        (add_split named_if_split base && [ExclX ("split:" ^ key)])

      (* Local attributes replace the former generic exporter callbacks;
         the live rules are private and TypeBase is excluded independently. *)
      val _ = enable_split_attribute ()
      val _ = ThmAttribute.local_attribute
        {name="simp_split_selftest_rule",attrname="split",args=[],thm=named_if_split}
      val _ = ThmAttribute.local_attribute
        {name="simp_split_selftest_asm_rule",attrname="split",args=[],thm=named_if_asm_split}
      val registered = Context.snapshot ()
      val persistent_base = (base ++ split_ss) && [ExclX "case:bool"]
      val _ = tprint "persistent split replay control really splits"
      val _ = case valid (SIMP_TAC persistent_base []) split_goal of
          [([],result)] =>
            if not (aconv result (#2 split_goal)) andalso
               not (can (find_term is_cond) result)
            then OK () else die "persistent split control did not split"
        | _ => die "persistent split control produced wrong subgoals"
      val deleted = persistent_base &&
        [ExclX ("split:" ^ key),ExclX ("split:" ^ asm_key),
         ExclX "case:bool",ExclX ("split:" ^ key)]
      val _ = replay_checks "persistent split exclusion history" deleted
      val mixed_rules = persistent_base ++ rewrites_with_names
        [({Thy=thy,Name="split_replay_rule"},disposable)]
      val mixed_deleted = mixed_rules &&
        [Excl "split_replay_missing",ExclX ("rule:" ^ thy ^
           "$split_replay_rule"),Excl "split_replay_rule",
         ExclX ("split:" ^ key),Excl "split_replay_missing",
         ExclX ("split:" ^ asm_key),ExclX "case:bool"]
      val _ = replay_checks "mixed strict extended strategy history"
        mixed_deleted
      val _ = convtest
        ("mixed strict extended rule batch survives strategy replay",
         QCONV (SIMP_CONV
           (remove_ssfrags [dummy] mixed_deleted) []),
         ``replay_disposable:bool``, ``replay_disposable:bool``)
      val _ = check_goal "persistent assumption split exclusion replay"
        (remove_ssfrags [dummy] deleted) typebase_asm_goal
      val _ = Context.restore saved
      val _ = replay_checks "case exclusion after Context.restore"
        case_deleted
      val _ = check "local split exclusion after Context.restore"
        (remove_ssfrags [dummy] local_readded)
      (* Replay while the persistent target is absent, then restore its
         registration. Neither resolution nor ambient state may replace
         the recorded exclusion identity. *)
      val absent_replayed = remove_ssfrags [dummy] deleted
      val _ = Context.restore registered
      val _ = check "persistent split exclusion after Context.restore"
        absent_replayed
      val _ = replay_checks "restored persistent split exclusion" deleted
    in () end
  in Portable.finally (fn () => Context.restore saved) run () end

  (* The dot in the display name is parsed strictly by bare Excl. *)
  val _ = shouldfail
    {testfn=fn () =>
       runtac (VALID
         (SIMP_TAC (bool_ss ++ split_ss) [Excl "split.case bool"]))
         split_goal,
     printresult=K "unexpected success",
     printarg=K "bare split.case Excl rejects its theory part",
     checkexn=fn HOL_ERR error =>
       String.isSubstring "bad theory name" (Feedback.message_of error)
       | _ => false} ()

  val _ = shouldfail
    {testfn=fn () =>
       runtac (VALID
         (SIMP_TAC (bool_ss ++ split_ss)
           [ExclX "case:definitely_not_a_type"])) split_goal,
     printresult=K "unexpected success",
     printarg=K "nonexistent split.case exclusion",
     checkexn=fn HOL_ERR error =>
       String.isSubstring "did not match" (Feedback.message_of error)
       | _ => false} ()

  val limited_split_ss = limit 1 (bool_ss ++ split_ss)
  val limited_goal =
    ([], ``P (if b then x:'a else y) /\
           Q (if c then u:'b else v)``)
  val _ = tprint "simpset limit bounds splitter rounds"
  val _ =
    case valid (SIMP_TAC limited_split_ss []) limited_goal of
        [(_,result)] =>
          if not (aconv result (#2 limited_goal)) andalso
             can (find_term is_cond) result
          then OK()
          else die "splitter limit did not stop after one round"
      | _ => die "bounded splitter produced the wrong subgoals"

  val asm_goal =
    ([``P (if b then x:'a else y) : bool``], ``G:bool``)
  val with_asm_split = add_split named_if_asm_split bool_ss
  val _ = tprint "add_split auto-routes an assumption split rule"
  val _ =
    case valid (SIMP_TAC with_asm_split []) asm_goal of
        [_, _] => OK()
      | _ => die "assumption split rule was not routed to the asm looper"
in
  ()
end

(* ---------------------------------------------------------------------- *)
(* Split markers that cannot become split rules.                           *)

val _ = let
  (* A rule of the right shape but under no name in the theorem database
     -- what [type_split_of] derives -- is registered under its split
     redex's head constant, and a theorem that has a name but is not a
     split rule at all is dropped.  Neither may stop a tactic, and the
     rule list is the path on which the user hears about the drop. *)
  val bool_split = type_split_of ``:bool``
  val unnamed_split =
    INST_TYPE (map (fn v => v |-> ``:'zz -> 'zz``)
                   (type_vars_in_term (concl bool_split)))
              bool_split
  (* The instantiated rule matches only at the type it was instantiated
     to, so the goal is stated there: at [:'a] the rule would be
     inapplicable and the two outcomes -- dropped, and not matching --
     would look the same. *)
  val split_goal = ([], ``P (if b then (x:'zz -> 'zz) else y) : bool``)

  val warnings = ref ([] : string list)
  val saved_outstream = !Feedback.WARNING_outstream
  val _ = Feedback.WARNING_outstream := (fn s => warnings := s :: !warnings)
  fun warned () = List.exists (String.isSubstring "Split") (!warnings)
  fun run tac goal = Lib.total (fn () => valid tac goal) ()

  val _ = warnings := []
  val _ = tprint "unnamed Split rule splits under its head constant"
  val _ =
    case run (SIMP_TAC bool_ss [Split unnamed_split]) split_goal of
        NONE => die "unnamed Split rule aborted SIMP_TAC"
      | SOME [([], result)] =>
          if aconv result (#2 split_goal) then
            die "unnamed Split rule left the goal alone"
          else if warned () then
            die "unnamed Split rule was reported unusable"
          else OK()
      | SOME _ => die "unnamed Split rule produced the wrong subgoals"

  val _ = warnings := []
  val _ = tprint "an unnamed Split rule is retracted by its head constant"
  val _ =
    let
      val name = split_thm_name unnamed_split
      val retracted = del_split name (add_split unnamed_split bool_ss)
    in
      case run (SIMP_TAC retracted []) split_goal of
          NONE => die "the retracted split rule aborted SIMP_TAC"
        | SOME [([], result)] =>
            if aconv result (#2 split_goal) then OK()
            else die "the split rule survived its retraction"
        | SOME _ => die "the retracted split rule produced wrong subgoals"
    end

  val _ = warnings := []
  val _ = tprint "malformed Split rule leaves SIMP_TAC alone"
  val _ =
    case run (SIMP_TAC bool_ss [Split boolTheory.CONJ_COMM]) split_goal of
        NONE => die "malformed Split rule aborted SIMP_TAC"
      | SOME [([], result)] =>
          if not (aconv result (#2 split_goal)) then
            die "malformed Split rule changed the goal"
          else if not (warned ()) then
            die "malformed Split rule was dropped without a warning"
          else OK()
      | SOME _ => die "malformed Split rule produced the wrong subgoals"

  (* An assumption headed by the marker is a term the user is reasoning
     about rather than a rule the user asked for, and the tactics that
     scan assumptions are documented never to fail. *)
  val split_asm = concl (Split (ASSUME ``p /\ q``))
  val asm_goal = ([split_asm], ``r:bool``)
  val gcfg = {droptrues=true,elimvars=false,strip=true,oldestfirst=true}

  val _ = warnings := []
  val _ = tprint "Split-headed assumption does not abort global_simp_tac"
  val _ =
    case run (global_simp_tac gcfg bool_ss []) asm_goal of
        NONE => die "Split-headed assumption aborted global_simp_tac"
      | SOME _ => OK()

  val _ = warnings := []
  val _ = tprint "Split-headed assumption does not abort ASM_SIMP_TAC"
  val _ =
    case run (ASM_SIMP_TAC bool_ss []) asm_goal of
        NONE => die "Split-headed assumption aborted ASM_SIMP_TAC"
      | SOME _ => OK()

  val _ = Feedback.WARNING_outstream := saved_outstream
in
  ()
end

(* RW_TAC's final IF_CASES_TAC phase solves all of these, so they mark a
   conditional-splitting strength floor for the opt-in splitter.  The
   expectations are fixed here rather than compared against RW_TAC live
   because RW_TAC lives far downstream of this directory. *)
val _ = let
  fun solves goal =
    null (valid (SIMP_TAC (bool_ss ++ split_ss) []) ([],goal))
  fun check (name,goal) =
    (tprint ("split_ss strength: " ^ name);
     if solves goal then OK()
     else die "goal was not solved by bool_ss ++ split_ss")
in
  List.app check
    [("conditional chooses one branch",
      ``(if b then x:'a else y) = x \/ (if b then x else y) = y``),
     ("boolean conditional implication",
      ``(if b then p else q) ==> p \/ q``),
     ("conditional occurs in opposite equality sides",
      ``(if b then x:'a else y) = x \/ y = (if b then x else y)``),
     ("nested conditional condition",
      ``(if (if b then c else d) then x:'a else y) = x \/
        (if (if b then c else d) then x else y) = y``),
     ("conditional under an application",
      ``f (if b then x:'a else y) = f x \/
        f (if b then x else y) = f y``)]
end

(* The gs family downstream differs only in this configuration record;
   strip=false (bossLib's gns) must return assumptions whole rather than
   stripped. *)
val _ = let
  val cfg = {elimvars=false,strip=false,droptrues=true,oldestfirst=true}
  val goal = ([``p /\ q``], ``r:bool``)
  val _ = tprint "global_simp_tac strip=false keeps assumptions whole"
in
  case valid (global_simp_tac cfg bool_ss []) goal of
      [([asm], w)] =>
        if aconv asm ``p /\ q`` andalso aconv w ``r:bool`` then OK()
        else die "strip=false changed the goal"
    | _ => die "strip=false produced the wrong subgoals"
end

(* ---------------------------------------------------------------------- *)
(* Mutual global simplification and extended fixpoint controls.            *)

val _ = let
  val base_cfg =
    {droptrues=true,elimvars=false,strip=false,oldestfirst=true}
  fun mode_xcfg mode concl rebuild =
    GEN_GLOBAL_SIMP_TAC mode
      {base=base_cfg,concl_in_fixpoint=concl,imp_rebuild=rebuild,
       imp_premises=false}
  val xcfg = mode_xcfg {safe=false}
  fun result tac goal = valid tac goal
  fun check msg expected tac goal =
    let val _ = tprint msg
    in
      case result tac goal of
          actual =>
            if list_eq goal_eq expected actual then OK()
            else die (msg ^ " produced " ^
                      String.concatWith ", " (map printgoal actual))
    end

  val mutual_goal =
    ([``P (a:'a) : bool``, ``a:'a = b``], ``mutual_q:bool``)
  val mutual_expected =
    [([``P (b:'a) : bool``, ``a:'a = b``], ``mutual_q:bool``)]
  val _ =
    check "GEN_GLOBAL_SIMP_TAC uses later assumptions mutually"
      mutual_expected
      (xcfg false false bool_ss []) mutual_goal

  val chain_goal =
    ([``(f:'a -> 'b) x = g x``, ``(g:'a -> 'b) x = z``,
      ``R ((f:'a -> 'b) x) : bool``], ``chain_s:bool``)
  val chain_expected =
    [([``(f:'a -> 'b) x = z``, ``(g:'a -> 'b) x = z``,
       ``R (z:'b) : bool``], ``chain_s:bool``)]
  val _ =
    check "GEN_GLOBAL_SIMP_TAC closes a three-assumption mutual chain"
      chain_expected
      (xcfg false false bool_ss []) chain_goal

  (* A premise written as an antecedent of the conclusion reaches the
     simplifier through the implication congruence, which offers it only
     the antecedents before it; imp_premises discharges them first, so
     the fixpoint has them all. *)
  fun premise_xcfg concl rebuild =
    GEN_GLOBAL_SIMP_TAC {safe=false}
      {base=base_cfg,concl_in_fixpoint=concl,imp_rebuild=rebuild,
       imp_premises=true}
  val premise_goal =
    ([] : term list, ``P (a:'a) ==> (a:'a = b) ==> mutual_q:bool``)
  val _ =
    check "antecedents stay out of the fixpoint without imp_premises"
      [premise_goal]
      (Tactical.TRY (xcfg false false bool_ss [])) premise_goal
  val _ =
    check "imp_premises brings the antecedents into the fixpoint"
      [([``a:'a = b``, ``P (b:'a) : bool``], ``mutual_q:bool``)]
      (premise_xcfg false false bool_ss []) premise_goal

  val mode_goal =
    ([``global_mode_assumption:bool``],``?b:bool. b``)
  val mode_ss =
    add_unsafe_solver
      (mk_tactic_solver
         ("global unsafe instantiation",
          Q.EXISTS_TAC `T` THEN ACCEPT_TAC TRUTH))
      empty_ss
  val safe_mode_result =
    result (mode_xcfg {safe=true} true false mode_ss []) mode_goal
  val unsafe_mode_result =
    result (xcfg true false mode_ss []) mode_goal
  val _ =
    tprint "safe global simp does not use unsafe final instantiation"
  val _ =
    if list_eq goal_eq [mode_goal] safe_mode_result andalso
       null unsafe_mode_result
    then OK()
    else die "global simp mode selected the wrong final-solver list"

  val side_condition =
    ``global_safe_side_p \/ ~global_safe_side_p``
  val side_condition_th =
    SPEC ``global_safe_side_p:bool`` boolTheory.EXCLUDED_MIDDLE
  val side_lhs =
    ``if global_safe_side_p \/ ~global_safe_side_p
      then global_safe_side_x:'a
      else global_safe_side_y``
  val side_rhs = ``global_safe_side_x:'a``
  val side_rule =
    DISCH side_condition
      (REWRITE_CONV [ASSUME side_condition] side_lhs)
  val side_solver_calls = ref 0
  fun side_solver _ tm =
    (side_solver_calls := !side_solver_calls + 1;
     if aconv tm side_condition then side_condition_th
     else
       raise mk_HOL_ERR "selftest" "side_solver"
                         "not the global safe side condition")
  val side_ss =
    empty_ss ++ rewrites [side_rule]
    |> add_unsafe_solver
         {name="global safe traversal side condition",solve=side_solver}
  val side_goal = ([],mk_comb(``global_safe_side_Q:'a -> bool``,side_lhs))
  val side_expected =
    [([],mk_comb(``global_safe_side_Q:'a -> bool``,side_rhs))]
  val _ =
    check "safe global simp uses unsafe traversal side-condition solvers"
      side_expected
      (mode_xcfg {safe=true} false false side_ss [])
      side_goal
  val _ =
    if !side_solver_calls > 0 then ()
    else die "safe global simp skipped the traversal side-condition solver"

  val schedule_a = ``schedule_a:bool``
  val schedule_b0 = ``schedule_b /\ T``
  val schedule_b1 = ``schedule_b:bool``
  val schedule_c = ``schedule_c:bool``
  val schedule_calls = Array.array (4,0)
  fun increment i =
    Array.update (schedule_calls,i,Array.sub (schedule_calls,i) + 1)
  fun schedule_conv _ _ tm =
    if aconv tm schedule_a then (increment 0; NO_CONV tm)
    else if aconv tm schedule_b0 then
      (increment 1; REWRITE_CONV [boolTheory.AND_CLAUSES] tm)
    else if aconv tm schedule_b1 then (increment 2; NO_CONV tm)
    else if aconv tm schedule_c then (increment 3; NO_CONV tm)
    else NO_CONV tm
  val schedule_ss =
    empty_ss ++
    conv_ss {name="global schedule probe",key=NONE,trace=0,
             conv=schedule_conv}
  val schedule_goal =
    ([schedule_a,schedule_b0,schedule_c], ``schedule_goal:bool``)
  val schedule_expected =
    [([schedule_a,schedule_b1,schedule_c], ``schedule_goal:bool``)]
  val schedule_result =
    result (xcfg false false schedule_ss []) schedule_goal
  val _ = tprint "global change counting skips the provably-fixed tail"
  val _ =
    if list_eq goal_eq schedule_expected schedule_result andalso
       List.tabulate (4,fn i => Array.sub (schedule_calls,i)) = [1,1,1,2]
    then OK()
    else die "global change-count schedule did not skip the fixed tail"

  val conclusion_calls = ref 0
  fun conclusion_probe _ _ tm =
    if aconv tm (#2 schedule_goal) then
      (conclusion_calls := !conclusion_calls + 1; NO_CONV tm)
    else NO_CONV tm
  val per_pass_ss =
    schedule_ss ++
    conv_ss {name="global conclusion pass probe",key=NONE,trace=0,
             conv=conclusion_probe}
  val _ =
    result (xcfg true false per_pass_ss []) schedule_goal
  val _ = tprint "concl_in_fixpoint simplifies the conclusion each pass"
  val _ =
    if !conclusion_calls = 2 then OK()
    else die "conclusion was not simplified on every assumption pass"

  val noop_a = ``global_noop_a:bool``
  val noop_nested = ref false
  fun noop_conv _ _ tm =
    if aconv tm noop_a then
      if !noop_nested then (noop_nested := false; NO_CONV tm)
      else
        let
          val _ = noop_nested := true
          val collapse =
            REWRITE_CONV [boolTheory.AND_CLAUSES]
                         (mk_conj (noop_a,boolSyntax.T))
        in
          SYM collapse
        end
    else NO_CONV tm
  val noop_ss =
    empty_ss ++
    conv_ss {name="global net-noop probe",key=NONE,trace=0,
             conv=noop_conv}
  val noop_cfg =
    {droptrues=true,elimvars=false,strip=true,oldestfirst=true}
  val _ =
    check "global structural net-noop pass terminates"
      [([noop_a],``global_noop_goal:bool``)]
      (GEN_GLOBAL_SIMP_TAC
         {safe=false}
         {base=noop_cfg,concl_in_fixpoint=false,imp_rebuild=false,
          imp_premises=false}
         noop_ss [])
      ([noop_a],``global_noop_goal:bool``)

  val fix_asm0 = ``fix_asm_p /\ T``
  val fix_asm1 = ``fix_asm_p:bool``
  val fix_concl0 = ``fix_concl_p /\ T``
  val fix_concl1 = ``fix_concl_p:bool``
  val unlocked = ref false
  fun gate_conv _ _ tm =
    if aconv tm fix_concl0 then
      (unlocked := true; REWRITE_CONV [boolTheory.AND_CLAUSES] tm)
    else if !unlocked andalso aconv tm fix_asm0 then
      REWRITE_CONV [boolTheory.AND_CLAUSES] tm
    else NO_CONV tm
  val gate_ss =
    empty_ss ++
    conv_ss {name="global conclusion gate",key=NONE,trace=0,
             conv=gate_conv}
  val gate_goal = ([fix_asm0],fix_concl0)
  val _ = unlocked := false
  val _ =
    check "default global simplification keeps conclusion outside fixpoint"
      [([fix_asm0],fix_concl1)]
      (xcfg false false gate_ss []) gate_goal
  val _ = unlocked := false
  val _ =
    check "concl_in_fixpoint restarts changed assumptions"
      [([fix_asm1],fix_concl1)]
      (xcfg true false gate_ss []) gate_goal

  val once_p = ``global_once_p:bool``
  val once_rule = CONJUNCT1 (SPEC once_p boolTheory.AND_CLAUSES)
  val once_goal = ([],mk_conj(boolSyntax.T,mk_conj(boolSyntax.T,once_p)))
  val _ =
    check "global supplied Once rewrite is installed exactly once"
      [([],mk_conj(boolSyntax.T,once_p))]
      (xcfg false false empty_ss [Once once_rule])
      once_goal

  val once_asm_p = ``global_once_asm_p:bool``
  val once_concl_p = ``global_once_concl_p:bool``
  val once_across_goal =
    ([mk_conj(boolSyntax.T,once_asm_p)],
     mk_conj(boolSyntax.T,once_concl_p))
  val _ =
    check "global supplied Once lifetime spans assumptions and conclusion"
      [([once_asm_p],mk_conj(boolSyntax.T,once_concl_p))]
      (xcfg false false empty_ss [Once once_rule])
      once_across_goal

  val local_exclsf = concl (ExclSF "BOOL")
  val local_exclsf_target = ``T /\ global_local_exclsf_p``
  (* The target is popped first, leaving ExclSF in the local context. *)
  val local_exclsf_goal =
    ([local_exclsf,local_exclsf_target],``global_local_exclsf_q:bool``)
  val _ =
    check "global remaining ExclSF applies while simplifying assumptions"
      [local_exclsf_goal]
      (xcfg false false bool_ss [])
      local_exclsf_goal

  val once_exclsf_asm = ``T /\ global_once_exclsf_asm_p``
  val once_exclsf_concl = ``T /\ global_once_exclsf_concl_p``
  val once_exclsf_goal =
    ([local_exclsf,once_exclsf_asm],once_exclsf_concl)
  val _ =
    check "global ExclSF rebuild preserves supplied Once lifetime"
      [([local_exclsf,``global_once_exclsf_asm_p:bool``],
         once_exclsf_concl)]
      (xcfg false false bool_ss [Once once_rule])
      once_exclsf_goal

  val supplied_sentinel = REFL ``global_supplied_sentinel:'a``
  fun has_only_untagged_sentinel thms =
    let
      val sentinels =
        List.filter
          (fn th => aconv (concl th) (concl supplied_sentinel))
          thms
    in
      not (null sentinels) andalso
      List.all (not o can BoundedRewrites.DEST_BOUNDED) sentinels
    end
  val supplied_condition =
    SPEC ``global_traversal_p:bool`` boolTheory.EXCLUDED_MIDDLE
  val supplied_solver_calls = ref 0
  fun supplied_solver {context_thms,...} tm =
    let
      val has_sentinel = has_only_untagged_sentinel context_thms
      val _ = supplied_solver_calls := !supplied_solver_calls + 1
    in
      if aconv tm (concl supplied_condition) andalso has_sentinel then
        supplied_condition
      else
        raise mk_HOL_ERR "selftest" "supplied_solver"
                          "supplied theorem absent from traversal context"
    end
  val supplied_tm = concl supplied_condition
  val supplied_rule =
    DISCH supplied_tm (EQT_INTRO (ASSUME supplied_tm))
  val supplied_ss =
    empty_ss ++ rewrites [supplied_rule]
    |> add_unsafe_solver
         {name="global supplied traversal context",solve=supplied_solver}
  val _ = supplied_solver_calls := 0
  val _ =
    check "global traversals see supplied source theorem without bound tag"
      []
      (xcfg false false supplied_ss [Once supplied_sentinel])
      ([supplied_tm],supplied_tm)
  val _ =
    if !supplied_solver_calls >= 2 then ()
    else die "global assumption or conclusion traversal skipped its solver"

  val root_target = ``root_a ==> root_b``
  val root_result = ``root_c ==> root_d``
  val root_condition = ``(root_side_P:bool -> bool) (T /\ T)``
  val root_rule =
    ASSUME (mk_imp (root_condition,mk_eq (root_target,root_result)))
  val root_context = ASSUME ``(root_side_P:bool -> bool) T``
  val root_ss =
    pureSimps.pure_ss ++ rewrites [boolTheory.AND_CLAUSES,root_rule]
  val _ = convtest
    ("root rewriting fully simplifies conditional-rule side conditions",
     Traverse.ROOT_REWRITE (xtraversedata_for_ss root_ss) [root_context],
     root_target,root_result)

  val imp_goal = ([``imp_p:bool``],``imp_q:bool``)
  val imp_ss =
    empty_ss ++ rewrites [Once (GSYM boolTheory.CONTRAPOS_THM)]
  val _ =
    check "imp_rebuild rewrites a discharged assumption at the root"
      [([``~imp_q``],``~imp_p``)]
      (xcfg false true imp_ss []) imp_goal

  val excluded_imp_name = "global excluded implication rebuild"
  val excluded_imp_marker = concl (ExclSF excluded_imp_name)
  val excluded_imp_target = ``excluded_imp_a ==> excluded_imp_q``
  fun excluded_imp_conv _ _ tm =
    if aconv tm excluded_imp_target then
      REWR_CONV (GSYM boolTheory.CONTRAPOS_THM) tm
    else NO_CONV tm
  val excluded_imp_ss =
    empty_ss ++
    name_ss excluded_imp_name
      (conv_ss
         {name=excluded_imp_name,key=SOME ([],excluded_imp_target),trace=0,
          conv=excluded_imp_conv})
  val excluded_imp_goal =
    ([``excluded_imp_a:bool``,excluded_imp_marker],
     ``excluded_imp_q:bool``)
  val _ =
    check "imp_rebuild applies remaining ExclSF before root rewriting"
      [excluded_imp_goal]
      (xcfg false true excluded_imp_ss [])
      excluded_imp_goal

  val supplied_imp_target =
    ``global_supplied_imp_a ==> global_supplied_imp_b``
  exception SUPPLIED_IMP_CONTEXT of bool
  fun supplied_imp_has_context context =
    (raise context) handle SUPPLIED_IMP_CONTEXT present => present
                         | _ => false
  fun supplied_imp_addcontext (context,thms) =
    let
      val has_source = has_only_untagged_sentinel thms
    in
      SUPPLIED_IMP_CONTEXT
        (supplied_imp_has_context context orelse has_source)
    end
  fun supplied_imp_apply {solver,stack,context,...} tm =
    if aconv tm supplied_imp_target then
      (supplied_imp_has_context context orelse
       raise mk_HOL_ERR "selftest" "supplied_imp_apply"
                         "supplied source theorem absent from dproc context";
       solver stack supplied_tm;
       REWR_CONV (GSYM boolTheory.CONTRAPOS_THM) tm)
    else NO_CONV tm
  val supplied_imp_reducer =
    lifted_reducer
      {name=SOME "global supplied implication rebuild",
       initial=SUPPLIED_IMP_CONTEXT false,
       addcontext=supplied_imp_addcontext,
       apply=supplied_imp_apply}
  val supplied_imp_ss =
    empty_ss ++ dproc_ss supplied_imp_reducer
    |> add_unsafe_solver
         {name="global supplied traversal context",solve=supplied_solver}
  val _ =
    check "imp_rebuild sees supplied theorems in its traversal context"
      [([``~global_supplied_imp_b``],
         ``~global_supplied_imp_a``)]
      (xcfg false true supplied_imp_ss [Once supplied_sentinel])
      ([``global_supplied_imp_a:bool``],
       ``global_supplied_imp_b:bool``)
in
  ()
end

(* The simpset layer must never use a directive as a rewrite: requirement
   directives are refused (their marker$ hypothesis would otherwise reach
   the result), tactic-only ones are dropped. *)
val _ =
  let
    val q = mk_var("q", bool)
    val th = ASSUME q
    fun refuses (name, d) =
        (tprint ("SIMP_CONV refuses " ^ name);
         shouldfail {testfn = fn l => SIMP_CONV bool_ss l q,
                     printresult = thm_to_string,
                     printarg = fn _ => name,
                     checkexn = check_HOL_ERRexn
                                  (fn (_, f, _) => f = "process_tags")}
                    [d])
    fun drops (name, d, t) =
        (tprint ("SIMP_CONV drops " ^ name);
         require_msg (check_result (fn th => rhs (concl th) ~~ t))
                     thm_to_string (QCONV (SIMP_CONV bool_ss [d])) t)
  in
    List.app refuses [("Req0", Req0 th), ("ReqD", ReqD th)];
    List.app drops [("NoAsms", markerLib.NoAsms, concl markerLib.NoAsms),
                    ("IgnAsm", markerLib.IgnAsm ‘x = _’,
                     concl (markerLib.IgnAsm ‘x = _’))]
  end

(* Explicit exclusions, including bounded payloads, are controls, not
   rewrite facts. Requirements still enclose them and remain tactic-only. *)
val _ =
  let
    fun check name b = (tprint name; if b then OK () else die name)
    val tm = ``T /\ (exclusion_boundary_p:bool)``
    val rule = CONJUNCT1 (SPEC_ALL boolTheory.AND_CLAUSES)
    val ss = empty_ss ++ rewrites_with_names
      [({Thy="",Name="boundary_rule"},rule)]
    val x = ExclX "rule:boundary_rule"
    val markers = [("ExclX", x), ("Once ExclX", Once x),
                   ("Ntimes ExclX", Ntimes x 3)]
    fun routes (name,th) =
      let
        val (prepared,rest) = prepare_rewrite_arguments ss [th]
        val result = QCONV (SIMP_CONV prepared rest) tm
        val direct = QCONV (SIMP_CONV ss [th]) tm
        val via_and = QCONV (SIMP_CONV (ss && [th]) []) tm
        val (goals,_) = runtac (VALID (SIMP_TAC ss [th])) ([],tm)
      in
        check (name ^ " routes without leaking marker hypotheses")
          (null rest andalso null (hyp result) andalso
           aconv (concl result) (mk_eq (tm,tm)) andalso
           aconv (concl direct) (concl result) andalso null (hyp direct)
           andalso aconv (concl via_and) (concl result)
           andalso null (hyp via_and) andalso
           case goals of [([],g)] => aconv g tm | _ => false)
      end
    fun requirement (name,th) =
      (shouldfail
         {testfn=fn () => SIMP_CONV ss [th] tm,
          printarg=K (name ^ " remains tactic-only"),
          printresult=thm_to_string,
          checkexn=check_HOL_ERRexn
            (fn (_,f,msg) => f = "process_tags" andalso
                            String.isSubstring "tactic directive" msg)} ();
       check (name ^ " is stripped before tactic exclusion")
         (null (valid (SIMP_TAC ss [th]) ([],T)));
       check (name ^ " suppresses the active rewrite on an unsolved goal")
         (list_eq goal_eq (valid (SIMP_TAC ss [th]) ([],tm)) [([],tm)]))
    fun typo name = shouldfail
      {testfn=fn () => empty_ss && [ExclX name],
       printarg=K ("ExclX rejects missing " ^ name),
       printresult=K "unexpected success",
       checkexn=check_HOL_ERRexn
         (fn (_,f,msg) => f = "process_tags" andalso
                         String.isSubstring "did not match" msg)} ()
  in
    convtest ("ExclX boundary fixture is an active rewrite",
              SIMP_CONV ss [],tm,``exclusion_boundary_p:bool``);
    List.app routes markers;
    List.app requirement [("Req0 ExclX",Req0 x),
                          ("Req0 Once ExclX",Req0 (Once x))];
    shouldfail
      {testfn=fn () => runtac (VALID (SIMP_TAC ss [ReqD x])) ([],tm),
       printarg=K "ReqD ExclX still checks the requirement",
       printresult=K "unexpected success",
       checkexn=check_HOL_ERRexn
         (fn (_,f,_) => f = "REQUIRE_DECREASE_TAC")} ();
    List.app typo ["missing", "rule:missing", "looper:missing",
                   "solver:missing", "split:missing", "case:missing"]
  end

(* Extension namespace selection and collision matrix. The ordinary
   prefix/parser matrix lives in exclusion-contracts. *)
val _ = let
  fun check name b = (tprint name; if b then OK () else die name)
  fun silent label f = let
    val sink = !Feedback.WARNING_outstream
    val warnings = ref ([] : string list)
    val _ = Feedback.WARNING_outstream :=
      (fn s => (warnings := s :: !warnings; sink s))
    val result = Exn.capture f ()
    val _ = Feedback.WARNING_outstream := sink
    val _ = check (label ^ " is silent") (null (!warnings))
  in Exn.release result end
  val _ = check "namespace matrix warnings are enabled"
    (!Feedback.emit_WARNING andalso not (!Feedback.WARNINGs_as_ERRs))
  val em = SPEC ``matrix_p:bool`` boolTheory.EXCLUDED_MIDDLE
  val em2 = SPEC ``matrix_q:bool`` boolTheory.EXCLUDED_MIDDLE
  val goal = ([],mk_conj (concl em,concl em2))
  val split_goals = [([],concl em),([],concl em2)]
  val calls = ref 0
  fun solve _ tm =
    (calls := !calls + 1;
     if aconv tm (concl em) then em else NO_CONV tm)
  fun looper _ = CONJ_TAC
  val dummy = "extended matrix unrelated fragment"
  val base = empty_ss ++ name_ss dummy empty_ssfrag
  val shared = base |> add_looper ("matrix_shared",looper)
    |> add_unsafe_solver {name="matrix_shared",solve=solve}
    |> add_safe_solver {name="matrix_shared",solve=solve}
  fun goals label set markers expected = silent label (fn () => let
    val (actual,validate) = runtac (VALID (SIMP_TAC set markers)) goal
    val th = validate (map (ASSUME o #2) actual)
  in
    check label (list_eq goal_eq actual expected andalso
      aconv (concl th) (#2 goal) andalso
      HOLset.equal (hypset th,
        HOLset.fromList Term.compare (map #2 expected)))
  end)
  val _ = goals "namespace control looper and solver active"
    shared [] [([],concl em2)]
  val without_looper = silent "qualified looper construction"
    (fn () => shared && [ExclX "looper:matrix_shared"])
  val without_solver = silent "qualified solver construction"
    (fn () => shared && [ExclX "solver:matrix_shared"])
  val _ = goals "qualified looper really removes only the looper"
    without_looper [] [goal]
  val _ = calls := 0
  val _ = goals "qualified solver really removes only the solver"
    without_solver [] split_goals
  val _ = check "qualified solver suppresses unsafe callbacks" (!calls = 0)
  val _ = silent "qualified solver safe selection" (fn () =>
    check "qualified solver suppresses safe callbacks"
      (list_eq goal_eq
        (valid (GEN_SIMP_TAC {safe=true} without_solver []) goal)
        split_goals andalso !calls = 0))
  val _ = goals "ordinary looper exclusion replay"
    (remove_ssfrags [dummy] without_looper) [] [goal]
  val _ = goals "ordinary solver exclusion replay"
    (remove_ssfrags [dummy] without_solver) [] split_goals
  val _ = goals "ordinary looper later re-addition replay"
    (remove_ssfrags [dummy]
      (add_looper ("matrix_shared",looper) without_looper))
    [] [([],concl em2)]
  val _ = goals "ordinary solver later re-addition replay"
    (remove_ssfrags [dummy]
      (add_unsafe_solver {name="matrix_shared",solve=solve} without_solver))
    [] [([],concl em2)]
  fun rejects label expected set markers = silent label (fn () =>
    shouldfail
      {testfn=fn () => set && markers, printarg=K label,
       printresult=K "unexpected success",
       checkexn=check_HOL_ERRexn (fn (_,_,msg) =>
         String.isSubstring expected msg)} ())
  val _ = rejects "shared strategy ambiguity" "ambiguous" shared
    [ExclX "matrix_shared"]
  val _ = goals "qualified solver then bare looper ordering" shared
    [ExclX "solver:matrix_shared",ExclX "matrix_shared"] [goal]
  val _ = goals "qualified looper then bare solver ordering" shared
    [ExclX "looper:matrix_shared",ExclX "matrix_shared"] [goal]
  val relaxed_looper = add_looper ("matrix.qualified looper",looper) base
  val relaxed_solver = add_unsafe_solver
    {name="matrix.qualified solver",solve=solve}
    (add_looper ("matrix other looper",looper) base)
  val _ = goals "relaxed looper display control is active"
    relaxed_looper [] split_goals
  val _ = goals "relaxed solver display control is active"
    relaxed_solver [] [([],concl em2)]
  val _ = goals "qualified looper accepts a relaxed dotted display"
    relaxed_looper [ExclX "looper:matrix.qualified looper"] [goal]
  val _ = goals "qualified solver accepts a relaxed dotted display"
    relaxed_solver [ExclX "solver:matrix.qualified solver"] split_goals
  val _ = rejects "bare dotted looper retains strict parsing" "bad theory"
    relaxed_looper [ExclX "matrix.qualified looper"]
  val _ = rejects "bare dotted solver retains strict parsing" "bad theory"
    relaxed_solver [ExclX "matrix.qualified solver"]
  val _ = rejects "ordinary repeated looper is unmatched" "did not match"
    shared [ExclX "looper:matrix_shared",ExclX "looper:matrix_shared"]
  val _ = rejects "ordinary repeated solver is unmatched" "did not match"
    shared [ExclX "solver:matrix_shared",ExclX "solver:matrix_shared"]
  val _ = List.app (fn name =>
    rejects ("warning-sensitive missing " ^ name) "did not match" base
      [ExclX name])
    ["missing","rule:missing","looper:missing","solver:missing",
     "split:missing","case:missing"]

  (* Literal prefixed rules AND dprocs contest actual extended targets.
     Both literal stores must be deleted without touching those targets. *)
  val lhs = ``T /\ (matrix_literal:bool)``
  val dinput = ``F \/ (matrix_literal:bool)``
  val and_rule = CONJUNCT1 (SPEC_ALL boolTheory.AND_CLAUSES)
  val or_rule = List.nth (CONJUNCTS (SPEC_ALL boolTheory.OR_CLAUSES),2)
  val dproc_calls = ref 0
  fun literal_stores name set =
    set ++ rewrites_with_names [({Thy="",Name=name},and_rule)] ++
    dproc_ss (lifted_reducer
      {name=SOME name,initial=Fail "matrix context",
       addcontext=fn (ctxt,_) => ctxt,
       apply=fn _ => fn tm => (dproc_calls := !dproc_calls + 1;
                               REWR_CONV or_rule tm)})
  fun unchanged set tm = let
    val th = QCONV (SIMP_CONV set []) tm
  in aconv (concl th) (mk_eq (tm,tm)) andalso null (hyp th) end
  fun collision (name,set,active) = silent ("literal collision " ^ name)
    (fn () => let
      val _ = List.app (fn (label,ss) =>
        check (name ^ label ^ " unmatched literal preserves extended target")
          (active ss))
        [(" Excl",set && [Excl name]), (" -*",set -* [name]),
         (" replay",remove_ssfrags [dummy] (set && [Excl name]))]
      val installed = literal_stores name set
      val _ = convtest (name ^ " literal rewrite active",
        SIMP_CONV installed [],lhs,``matrix_literal:bool``)
      val _ = convtest (name ^ " literal dproc active",
        SIMP_CONV installed [],dinput,``matrix_literal:bool``)
      fun deleted (label,ss) = let
        val _ = dproc_calls := 0
      in
        check (name ^ label ^ " deletes both literal stores")
          (unchanged ss lhs andalso unchanged ss dinput andalso
           !dproc_calls = 0);
        check (name ^ label ^ " preserves the extended target") (active ss)
      end
    in
      List.app deleted
        [(" Excl",installed && [Excl name]),
         (" -*",installed -* [name]),
         (" replay",remove_ssfrags [dummy]
           (installed && [Excl name,Excl name]))]
    end)
  val target = ASSUME ``(matrix_rule_target:'a) = matrix_rule_result``
  val rule_set = base ++ rewrites_with_names
    [({Thy="",Name="matrix_rule"},target)]
  val _ = collision ("rule:matrix_rule",rule_set,fn ss =>
    aconv (rhs (concl (SIMP_CONV ss [] ``matrix_rule_target:'a``)))
      ``matrix_rule_result:'a``)
  val _ = collision ("looper:matrix_shared",shared,fn ss =>
    list_eq goal_eq (valid (SIMP_TAC ss []) goal) [([],concl em2)])
  val _ = collision ("solver:matrix_shared",shared,fn ss =>
    list_eq goal_eq (valid (SIMP_TAC ss []) goal) [([],concl em2)])
  val named_split = Feedback.quiet_messages save_thm
    ("matrix_split",type_split_of ``:bool``)
  val split_set = add_split named_split base
  val split_goal = ([],``P (if b then x:'a else y):bool``)
  fun active_split ss =
    case valid (SIMP_TAC ss []) split_goal of
      [([],tm)] => not (can (find_term is_cond) tm)
    | _ => false
  val _ = collision ("split:" ^ Theory.current_theory () ^ "$matrix_split",
                     split_set,active_split)
  val _ = collision ("case:bool",base ++ split_ss,active_split)

  val a = ``matrix_suffix_a:bool``
  val b = ``matrix_suffix_b:bool``
  val ghost = "matrix_nonancestor"
  val suffix_set = base ++ rewrites_with_names
    [({Thy=ghost,Name="suffix.1"},ASSUME (mk_eq (a,T))),
     ({Thy=ghost,Name="suffix.2"},ASSUME (mk_eq (b,T)))]
  val _ = rejects "bare ExclX keeps strict initial parsing" "bad theory"
    suffix_set [ExclX (ghost ^ ".suffix")]
  val _ = List.app (fn spelling => silent ("relaxed suffix " ^ spelling)
    (fn () => let
      val deleted = suffix_set && [ExclX ("rule:" ^ spelling)]
      fun result ss = unchanged ss a andalso
        aconv (rhs (concl (SIMP_CONV ss [] b))) T
    in
      check ("relaxed suffix sibling preservation " ^ spelling)
        (result deleted andalso result (remove_ssfrags [dummy] deleted))
    end)) [ghost ^ ".suffix.1",ghost ^ "$suffix.1"]
in () end

fun sources_after ss =
  uncurry rewrite_sources o prepare_rewrite_arguments ss;
fun child_policy charge keep : Traverse.child_first_policy =
  {charge=charge, keep_abstraction=keep};

fun abstraction_policy_fixture body =
  let
    open boolLib
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = Theory.new_theory "abstractionPolicyFixture"
        val c_def =
          new_definition
            ("policy_c_def", ``policy_c (f:'a -> 'b) (x:'a) = f x``)
        val _ = new_constant ("policy_p", Type.bool --> Type.bool)
        val _ = new_constant ("policy_x", Type.bool)
        val rule =
          Tactical.prove
            (``!(P:'a -> 'b) x. policy_c (\v. P v) x = P x``,
             Tactical.EVERY
               [Rewrite.REWRITE_TAC [c_def], Tactic.BETA_TAC,
                Rewrite.REWRITE_TAC []])
        val c = fst (strip_comb (lhs (concl (SPEC_ALL c_def))))
        val {Thy = c_thy, Name = c_name, ...} = dest_thy_const c
        fun keep tm =
          let
            val {Thy, Name, ...} = dest_thy_const (fst (strip_comb tm))
          in Thy = c_thy andalso Name = c_name end
          handle HOL_ERR _ => false
        val ss = simpLib.++ (simpLib.empty_ss, boolSimps.ETA_ss)
        val charges = ref 0
        fun charge () = charges := !charges + 1
        fun converted pred rules input output =
          let
            val theorem =
              Conv.QCONV
                (simpLib.SIMP_CONV_CHILD_FIRST (child_policy charge pred)
                   ss rules) input
          in
            aconv (lhs (concl theorem)) input andalso
            aconv (rhs (concl theorem)) output andalso null (hyp theorem)
          end
        val full = ``policy_c (\v. policy_p v) policy_x``
        val applied = ``policy_p policy_x``
        val partial = ``policy_c (\v. policy_p v)``
        val plain_partial = ``policy_c policy_p``
        val plain_full = ``policy_c policy_p policy_x``
        val parent = simpLib.SIMP_CONV ss [rule] full
        val binders =
          [``!v:bool. policy_p v``, ``?v:bool. policy_p v``,
           ``@v:bool. policy_p v``]
        val name = {Thy=Theory.current_theory (), Name="policy_source"}
        val installed = ss ++ rewrites_with_names [(name, rule)]
        val (sources, _) = rewrite_sources installed []
        val (extended, _) = rewrite_sources (installed ++ rewrites [rule]) []
        val (copied, _) = rewrite_sources (set_cond_depth 3 installed) []
        val (excluded, _) = sources_after installed [Excl "policy_source"]
        val (filtered, _) =
          rewrite_sources (filter_rewrites (fn _ => false) installed) []
        val (cleared, _) = rewrite_sources (clear_rules installed) []
        val (conversions, supplied) = rewrite_sources ss [rule]
        val source_metadata =
          length sources = 1 andalso length extended = 2 andalso
          Portable.pointer_eq (tl extended, sources) andalso
          Portable.pointer_eq (copied, sources) andalso
          null excluded andalso null filtered andalso null cleared andalso
          null conversions andalso length supplied = 1 andalso
          aconv (concl (hd supplied)) (concl rule)
      in
        body
          (converted keep [rule] full applied,
           converted keep [] partial partial,
           converted (fn _ => false) [rule] full plain_full,
           converted (fn _ => false) [] partial plain_partial,
           aconv (lhs (concl parent)) full andalso
             aconv (rhs (concl parent)) applied andalso null (hyp parent),
           List.all
             (fn tm => converted (fn _ => true) [] tm tm andalso
                       converted (fn _ => false) [] tm tm) binders,
           !charges > 0, source_metadata)
      end
  in
    Portable.finally (fn () => Context.restore saved) run ()
  end;

val result = abstraction_policy_fixture
  (fn (full, partial, false_full, false_partial, parent, binders,
       charges, sources) =>
    (print ("POLICY_RESULTS " ^
       String.concatWith " "
         (map Bool.toString
           [full, partial, false_full, false_partial, parent, binders,
            charges, sources]) ^ "\n");
     full andalso partial andalso false_full andalso false_partial andalso
     parent andalso binders andalso charges andalso sources));

val _ = (tprint "child-first policies protect full and partial clients";
         if result then OK () else die "abstraction policy unavailable");

fun prepared_normalization_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = Theory.new_theory "preparedNormalizationFixture"
        val g = new_definition ("prepared_g_def", ``prepared_g x = T``)
        val h = new_definition ("prepared_h_def", ``prepared_h x = T``)
        val c = new_definition
          ("prepared_c_def", ``prepared_c (x:bool) = T``)
        val reducer = Tactical.prove
          (``!x:bool. prepared_g x = prepared_h x``,
           Rewrite.REWRITE_TAC [g, h])
        val ss = simpLib.empty_ss && [Once reducer, c]
        val input = ``prepared_c (prepared_g (x:bool))``
        val expected = ``prepared_c (prepared_h (x:bool))``
        val charges = ref 0
        val stop = ref NONE
        exception Stopped
        fun charge () =
          (charges := !charges + 1;
           if !stop = SOME (!charges) then raise Stopped else ())
        val prepared = prepare_child_first (Traverse.charge_only charge) ss
        fun checked theorem output =
          null (hyp theorem) andalso aconv (lhs (concl theorem)) input
          andalso aconv (rhs (concl theorem)) output
        val first = #arguments prepared [] input
        val count = !charges
        val second = #arguments prepared [] input
        val _ = charges := 0
        val _ = stop := SOME count
        val stopped =
          ((ignore (#arguments prepared [] input); false)
           handle Stopped => true)
        val _ = stop := NONE
        val after_failure = #arguments prepared [] input
        val actual = QCONV (SIMP_CONV_CHILD_FIRST
          (Traverse.charge_only (fn () => ())) ss []) ``prepared_g (x:bool)``
        val exhausted =
          QCONV (SIMP_CONV_CHILD_FIRST (Traverse.charge_only (fn () => ()))
            ss []) ``prepared_g (x:bool)``
        val after_consumption = #arguments prepared [] input
        val still_exhausted = QCONV (SIMP_CONV_CHILD_FIRST
          (Traverse.charge_only (fn () => ())) ss []) ``prepared_g (x:bool)``
        val bare = prepare_child_first (Traverse.charge_only (fn () => ()))
          simpLib.empty_ss
        val keyless = simpLib.conv_ss
          {name="prepared opaque", key=NONE, trace=0,
           conv=fn _ => fn _ => Conv.NO_CONV}
        val opaque = prepare_child_first
          (Traverse.charge_only (fn () => ())) (simpLib.empty_ss ++ keyless)
      in
        checked first expected andalso checked second expected andalso
        count > 0 andalso stopped andalso checked after_failure expected
        andalso aconv (rhs (concl actual)) ``prepared_h (x:bool)``
        andalso aconv (rhs (concl exhausted)) ``prepared_g (x:bool)``
        andalso checked after_consumption expected
        andalso aconv (rhs (concl still_exhausted)) ``prepared_g (x:bool)``
        andalso #may_reduce_arguments prepared input
        andalso not (#may_reduce_arguments bare ``prepared_c (x:bool)``)
        andalso #may_reduce_arguments bare
                  ``eta_f (eta_g (\y:bool. eta_h y : bool)) : bool``
        andalso #may_reduce_arguments opaque ``prepared_c (x:bool)``
      end
  in
    Portable.finally (fn () => Context.restore saved) run ()
  end;

val _ = (tprint "prepared argument normalization preserves root and bounds";
         if prepared_normalization_fixture () then OK ()
         else die "prepared normalization changed root or rewrite allowance");

fun normalization_observer_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = Theory.new_theory "normalizationObserverFixture"
        val g = new_definition ("observer_g_def", ``observer_g x = T``)
        val h = new_definition ("observer_h_def", ``observer_h x = T``)
        val p = new_definition ("observer_p_def", ``observer_p x = T``)
        val c = new_definition
          ("observer_c_def", ``observer_c (x:bool) = T``)
        val rule = Tactical.prove
          (``!x:bool. observer_p x ==> (observer_g x = observer_h x)``,
           Rewrite.REWRITE_TAC [g,h,p])
        val ss = simpLib.empty_ss ++ rewrites [rule]
        val target = ``observer_c (observer_g (x:bool))``
        val condition = ``observer_p (x:bool)``
        val seen = ref ([] : term list)
        val observed_charges = ref 0
        val plain_charges = ref 0
        val observed = prepare_child_first_observed
          (fn tm => seen := tm :: !seen)
          (Traverse.charge_only
             (fn () => observed_charges := !observed_charges + 1)) ss
        val plain = prepare_child_first
          (Traverse.charge_only
             (fn () => plain_charges := !plain_charges + 1)) ss
        val first = #arguments observed [] target
        val second = #arguments plain [] target
        val same_charge = !observed_charges = !plain_charges
        val unchanged = ``observer_h (x:bool)``
        val untouched = #normalize observed [] unchanged
        fun visited tm = List.exists (aconv tm) (!seen)
        exception ObserverStopped
        val throwing = prepare_child_first_observed
          (fn tm => if aconv tm condition then raise ObserverStopped else ())
          (Traverse.charge_only (fn () => ())) ss
        val propagated =
          ((ignore (#arguments throwing [] target); false)
           handle ObserverStopped => true)
        val in_condition = ref false
        exception ChargeStopped
        val charged = prepare_child_first_observed
          (fn tm => if aconv tm condition then in_condition := true else ())
          (Traverse.charge_only
             (fn () => if !in_condition then raise ChargeStopped else ())) ss
        val charge_propagated =
          ((ignore (#arguments charged [] target); false)
           handle ChargeStopped => true)
        val hol_error = prepare_child_first_observed
          (fn tm => if aconv tm condition then
              raise mk_HOL_ERR "observer" "visit" "callback stopped"
            else ())
          (Traverse.charge_only (fn () => ())) ss
        val hol_error_propagated =
          ((ignore (#arguments hol_error [] target); false)
           handle HOL_ERR error =>
             Feedback.message_of error = "callback stopped")
      in
        let
          val checks =
            [null (hyp first), null (hyp second),
             aconv (concl first) (concl second),
             aconv (rhs (concl first)) target, same_charge,
             !plain_charges > 0,
             aconv (rhs (concl untouched)) unchanged,
             visited condition, visited unchanged,
             visited ``x:bool``, propagated, charge_propagated,
             hol_error_propagated]
          val _ = print ("OBSERVER_RESULTS " ^
            String.concatWith " " (map Bool.toString checks) ^ "\n")
        in List.all (fn passed => passed) checks end
      end
  in
    Portable.finally (fn () => Context.restore saved) run ()
  end;

val _ = (tprint "normalization observes unchanged and failed-condition terms";
         if normalization_observer_fixture () then OK ()
         else die "incomplete normalization dependencies or changed charges");

fun rewrite_view_control_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = Theory.new_theory "rewriteViewControlFixture"
        val g = new_definition ("view_g_def", ``view_g (x:bool) = T``)
        val h = new_definition ("view_h_def", ``view_h (x:bool) = T``)
        val c = new_definition ("view_c_def", ``view_c (x:bool) = T``)
        val d = new_definition ("view_d_def", ``view_d (x:bool) = T``)
        val k = new_definition ("view_k_def", ``view_k (x:bool) = T``)
        val reducer = Tactical.prove
          (``!x. view_g x = view_h x``, Rewrite.REWRITE_TAC [g,h])
        val original = Tactical.prove
          (``!x. view_c (view_g x) = view_k x``,
           Rewrite.REWRITE_TAC [c,k])
        val sibling = Tactical.prove
          (``!x. view_d (view_g x) = view_k x``,
           Rewrite.REWRITE_TAC [d,k])
        val x = ``x:bool``
        val view = GEN x
          (TRANS (SYM (AP_TERM ``view_c`` (SPEC x reducer)))
                 (SPEC x original))
        val name = {Thy=Theory.current_theory (),Name="view_source"}
        val original_tm = ``view_c (view_g x)``
        val view_tm = ``view_c (view_h x)``
        val sibling_tm = ``view_d (view_g x)``
        val result_tm = ``view_k x``
        fun frag rule =
          name_ss "view originals" (rewrites_with_names [(name,rule)])
        fun attach rule =
          let
            val ss = empty_ss ++ frag rule
            val source = hd (rewrite_source_handles ss)
          in ss ++ name_ss "views" (rewrite_views [(source,view)]) end
        fun conversion child ss =
          if child then
            SIMP_CONV_CHILD_FIRST (Traverse.charge_only (fn () => ())) ss []
          else SIMP_CONV ss []
        fun converted child ss input expected =
          let val th = QCONV (conversion child ss) input
          in null (hyp th) andalso aconv (lhs (concl th)) input andalso
             aconv (rhs (concl th)) expected end
        fun once child view_first =
          let
            val ss = attach (Once original)
            val (first,second) =
              if view_first then (view_tm,original_tm)
              else (original_tm,view_tm)
          in converted child ss first result_tm andalso
             converted child ss second second end
        fun twice child =
          let val ss = attach (Ntimes original 2)
          in converted child ss original_tm result_tm andalso
             converted child ss view_tm result_tm andalso
             converted child ss original_tm original_tm end
        val ss = attach (Once original)
        val _ = ignore (conversion false ss original_tm)
        val prepared =
          prepare_child_first (Traverse.charge_only (fn () => ())) ss
        val private_view = #normalize prepared [] view_tm
        val private_bound =
          aconv (rhs (concl private_view)) result_tm andalso
          converted false ss view_tm view_tm
        val replayed = remove_ssfrags ["unrelated"]
          (attach (Once original) ++
           name_ss "unrelated" (rewrites [Once sibling]))
        val replay_shared =
          converted false replayed view_tm result_tm andalso
          converted false replayed original_tm original_tm
        val removed = remove_ssfrags ["view originals"] (attach original)
        val filtered = filter_rewrites (fn _ => false) (attach original)
        val removal =
          converted false removed view_tm view_tm andalso
          converted false filtered view_tm view_tm andalso
          null (rewrite_source_handles removed) andalso
          null (rewrite_source_handles filtered)
        val exclusion = attach original -* ["view_source.1"]
        val excluded = converted false exclusion view_tm view_tm andalso
                       converted false exclusion original_tm original_tm
        fun multi_install () =
          let
            val multi =
              pureSimps.pure_ss ++ frag (Once (CONJ original sibling))
            val source = valOf (List.find
              (fn s => #1 (source_rewrite s) = SOME
                {Thy=Theory.current_theory (),Name="view_source.1"})
              (rewrite_source_handles multi))
          in multi ++ rewrite_views [(source,view)] end
        val multi_view = multi_install ()
        val sibling_shares =
          converted false multi_view view_tm result_tm andalso
          converted false multi_view sibling_tm sibling_tm
        val multi_excluded = multi_install () -* ["view_source.1"]
        val conjunct_exclusion =
          converted false multi_excluded view_tm view_tm andalso
          converted false multi_excluded sibling_tm result_tm
        val duplicate_frag = frag (Once original)
        val duplicate_ss = empty_ss ++ duplicate_frag ++ duplicate_frag
        val duplicate_sources = rewrite_source_handles duplicate_ss
        val duplicate_identity =
          length duplicate_sources = 2 andalso
          not (same_rewrite_source (hd duplicate_sources,
                                   hd (tl duplicate_sources)))
        val duplicate_view = duplicate_ss ++
          rewrite_views (map (fn s => (s,view)) duplicate_sources)
        val duplicate_allowances =
          converted false duplicate_view view_tm result_tm andalso
          converted false duplicate_view original_tm result_tm andalso
          converted false duplicate_view view_tm view_tm
        val raw_duplicates = empty_ss ++ rewrites
          [Once original,Once original]
        val raw_sources = rewrite_source_handles raw_duplicates
        val raw_identity = length raw_sources = 2 andalso
          not (same_rewrite_source (hd raw_sources,hd (tl raw_sources)))
        val merged_ss =
          empty_ss ++ merge_ss [duplicate_frag,duplicate_frag]
        val merged_sources = rewrite_source_handles merged_ss
        val merged_identity =
          length merged_sources = 2 andalso
          not (same_rewrite_source (hd merged_sources,hd (tl merged_sources)))
        val support_ss =
          empty_ss ++ frag (Once original) ++
          name_ss "other proof" (rewrites_with_names
            [(name,Once (TRANS (SPEC x original) (REFL result_tm)))])
        val actual_source = hd (tl (rewrite_source_handles support_ss))
        val support_views = support_ss ++ rewrite_views [(actual_source,view)]
        val support_removed = remove_ssfrags ["view originals"] support_views
        val proof_identity =
          converted false support_removed view_tm view_tm andalso
          converted false support_removed original_tm result_tm
        val support_filtered = filter_rewrites
          (fn (_,th) => not (aconv (concl th) (concl original))) support_views
        val filtered_proof_identity =
          converted false support_filtered view_tm view_tm andalso
          converted false support_filtered original_tm result_tm
        val stable_ss =
          attach original ++ name_ss "remove sibling" (rewrites [sibling])
        val stable = hd (tl (rewrite_source_handles stable_ss))
        val stable_replayed = remove_ssfrags ["remove sibling"] stable_ss
        val replay_identity =
          same_rewrite_source
            (stable,hd (rewrite_source_handles stable_replayed)) andalso
          converted false stable_replayed view_tm result_tm
        val filter_replayed = filter_rewrites
          (fn (_,th) => not (aconv (concl th) (concl sibling))) stable_ss
        val filter_identity =
          same_rewrite_source
            (stable,hd (rewrite_source_handles filter_replayed)) andalso
          converted false filter_replayed view_tm result_tm
        val native_only = length (rewrite_source_handles (attach original)) = 1
        val marker_excluded = QCONV
          (SIMP_CONV (attach original) [Excl "view_source.1"]) view_tm
        val marker_exclusion = aconv (rhs (concl marker_excluded)) view_tm
        val stale_base = empty_ss ++ frag original
        val stale_source = hd (rewrite_source_handles stale_base)
        val stale_views = (stale_base -* ["view_source.1"]) ++
          rewrite_views [(stale_source,view)]
        val stale_exclusion = converted false stale_views view_tm view_tm
        val ac_op = new_definition
          ("view_op_def", ``view_op (x:bool) (y:bool) = T``)
        val comm = Tactical.prove
          (``!x y. view_op x y = view_op y x``,
           Rewrite.REWRITE_TAC [ac_op])
        val assoc = Tactical.prove
          (``!x y z. view_op (view_op x y) z = view_op x (view_op y z)``,
           Rewrite.REWRITE_TAC [ac_op])
        val ac_base = empty_ss ++ ac_ss [(comm,assoc)]
        val ac_sources = rewrite_source_handles ac_base
        val ac_replayed = remove_ssfrags ["remove ac sibling"]
          (ac_base ++ name_ss "remove ac sibling" (rewrites [sibling]))
        val ac_identity = length ac_sources = 3 andalso
          ListPair.allEq same_rewrite_source
            (ac_sources,rewrite_source_handles ac_replayed) andalso
          not (same_rewrite_source (hd ac_sources,hd (tl ac_sources)))
        val checks =
          [once false false, once false true, once true false, once true true,
           twice false, twice true, private_bound, replay_shared, removal,
           excluded, sibling_shares, conjunct_exclusion, duplicate_identity,
           merged_identity, proof_identity, replay_identity, filter_identity,
           native_only, duplicate_allowances, raw_identity,
           filtered_proof_identity, marker_exclusion, stale_exclusion,
           ac_identity]
        val _ = print ("VIEW_CONTROL_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "rewrite views share source identity and replayed allowances";
         if rewrite_view_control_fixture () then OK ()
         else die "rewrite views lost their source or allowance");

(* Suspension removes one compiled conjunct, retaining history and quotas. *)
fun rewrite_suspension_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "rewriteSuspensionFixture"
        val g = new_definition ("susp_g_def", ``susp_g (x:bool) = T``)
        val h = new_definition ("susp_h_def", ``susp_h (x:bool) = T``)
        val c = new_definition ("susp_c_def", ``susp_c (x:bool) = T``)
        val d = new_definition ("susp_d_def", ``susp_d (x:bool) = T``)
        val k = new_definition ("susp_k_def", ``susp_k (x:bool) = T``)
        val u = new_definition ("susp_u_def", ``susp_u (x:bool) = T``)
        fun proof tm = Tactical.prove (tm,REWRITE_TAC [g,h,c,d,k,u])
        val original = proof ``!x. susp_c (susp_g x) = susp_k x``
        val sibling = proof ``!x. susp_d (susp_g x) = susp_k x``
        val unrelated = proof ``!x. susp_u x = susp_k x``
        val reducer = proof ``!x. susp_g x = susp_h x``
        val name = {Thy=current_theory (),Name="susp_source"}
        fun fragment th = name_ss "susp originals"
          (rewrites_with_names [(name,th)])
        val x = ``x:bool``
        fun view head source = GEN x
          (TRANS (SYM (AP_TERM head (SPEC x reducer))) (SPEC x source))
        val cview = view ``susp_c`` original
        val dview = view ``susp_d`` sibling
        fun source ss suffix = valOf (List.find
          (fn source => #1 (source_rewrite source) = SOME
            {Thy=current_theory (),Name="susp_source." ^ suffix})
          (rewrite_source_handles ss))
        fun installed th =
          let val ss = pureSimps.pure_ss ++ fragment th
          in ss ++ name_ss "susp views"
            (rewrite_views [(source ss "1",cview),(source ss "2",dview)])
          end
        val conj = CONJ original sibling
        val ctm = ``susp_c (susp_g x)``
        val dtm = ``susp_d (susp_g x)``
        val cvtm = ``susp_c (susp_h x)``
        val dvtm = ``susp_d (susp_h x)``
        val ktm = ``susp_k x``
        val utm = ``susp_u x``
        fun converted ss input expected =
          let val th = QCONV (SIMP_CONV ss []) input
          in null (hyp th) andalso aconv (rhs (concl th)) expected andalso
             null (valid (ACCEPT_TAC th) ([],mk_eq (input,expected))) end
        val ss = installed conj
        val selected = source ss "1"
        val retained = source ss "2"
        val suspended = suspend_rewrite_sources [selected] ss
        val native_removed = length (rewrite_source_handles suspended) + 1 =
          length (rewrite_source_handles ss)
        val original_removed = converted suspended ctm ctm
        val view_removed = converted suspended cvtm cvtm
        val sibling_active = converted suspended dtm ktm
        val sibling_view = converted suspended dvtm ktm
        val sibling_identity = same_rewrite_source
          (retained,source suspended "2")
        val source_unchanged = converted ss ctm ktm andalso
          converted ss cvtm ktm
        val dummy = name_ss "susp dummy" (rewrites [unrelated])
        val replayed = remove_ssfrags ["susp dummy"] (suspended ++ dummy)
        val replay = converted replayed ctm ctm andalso
          converted replayed cvtm cvtm andalso converted replayed dtm ktm
        val filtered = filter_rewrites
          (fn (_,th) => not (aconv (concl th) (concl unrelated)))
          (suspended ++ dummy)
        val filter_replay = converted filtered ctm ctm andalso
          converted filtered dtm ktm
        val excluded = suspended -* ["susp_source.2"]
        val exact_name = converted excluded dtm dtm andalso
          converted excluded dvtm dvtm andalso converted excluded ctm ctm
        val repeated = Portable.pointer_eq
          (suspend_rewrite_sources [selected] suspended,suspended)
        val empty = Portable.pointer_eq
          (suspend_rewrite_sources [] ss,ss)
        val other = installed conj
        val stale = Portable.pointer_eq
          (suspend_rewrite_sources [source other "1"] ss,ss)
        val deduplicated = suspend_rewrite_sources [selected,selected] ss
        val dedup = length (rewrite_source_handles deduplicated) =
          length (rewrite_source_handles suspended)
        val twice_installed =
          pureSimps.pure_ss ++ fragment conj ++ fragment conj
        val occurrences = List.filter
          (fn origin =>
            #1 (source_rewrite origin) = #1 (source_rewrite selected))
          (rewrite_source_handles twice_installed)
        val one_event = suspend_rewrite_sources [hd occurrences] twice_installed
        val event_identity = length (rewrite_source_handles one_event) + 1 =
          length (rewrite_source_handles twice_installed) andalso
          converted one_event ctm ktm
        val raw = empty_ss ++ rewrites [original,original]
        val one_slot = suspend_rewrite_sources
          [hd (rewrite_source_handles raw)] raw
        val slot_identity = length (rewrite_source_handles one_slot) = 1 andalso
          converted one_slot ctm ktm
        val once = installed (Once conj)
        val consumed = converted once ctm ktm
        val exhausted = suspend_rewrite_sources [source once "1"] once
        val quota = consumed andalso converted exhausted dtm dtm andalso
          converted exhausted dvtm dvtm
        val prepared = prepare_child_first
          (Traverse.charge_only (fn () => ())) exhausted
        val private_th = #normalize prepared [] dvtm
        val declared = aconv (rhs (concl private_th)) ktm andalso
          converted exhausted dvtm dvtm
        val twice = installed (Ntimes conj 2)
        val first = converted twice ctm ktm
        val remaining = suspend_rewrite_sources [source twice "1"] twice
        val partial_quota = first andalso converted remaining dvtm ktm andalso
          converted remaining dtm dtm andalso converted twice dtm dtm
        val unrelated_once = installed conj ++
          name_ss "susp bounded sibling" (rewrites [Once unrelated])
        val used_unrelated = converted unrelated_once utm ktm
        val unrelated_kept = suspend_rewrite_sources
          [source unrelated_once "1"] unrelated_once
        val other_quota = used_unrelated andalso
          converted unrelated_kept utm utm
        exception SuspContext of thm list
        val added = ref ([] : thm list)
        fun context_rules th = CONJUNCTS (SPEC_ALL th)
        fun is_original th = aconv (concl th) (concl (SPEC_ALL original))
        fun is_sibling th = aconv (concl th) (concl (SPEC_ALL sibling))
        val decision = Traverse.CONTEXT_REDUCER
          {name=SOME "susp context",initial=SuspContext [],
           addcontext=fn (SuspContext old,more) =>
             (added := List.concat (map context_rules more) @ !added;
              SuspContext (List.concat (map context_rules more) @ old))
             | _ => raise Fail "susp context",
           apply=fn {context,...} => fn tm =>
             case context of SuspContext rules =>
               if List.exists is_original rules then
                 REWR_CONV (SPEC_ALL original) tm else NO_CONV tm
               | _ => raise Fail "susp context"}
        val context_ss = pureSimps.pure_ss ++ dproc_ss decision ++ fragment conj
        val _ = added := []
        val context_suspended = suspend_rewrite_sources
          [source context_ss "1"] context_ss
        val context = not (List.exists is_original (!added)) andalso
          List.exists is_sibling (!added) andalso
          converted context_suspended ctm ctm andalso
          converted context_suspended dtm ktm
        val checks =
          [native_removed,original_removed,view_removed,sibling_active,
           sibling_view,sibling_identity,source_unchanged,replay,filter_replay,
           exact_name,repeated,empty,stale,dedup,event_identity,slot_identity,
           quota,declared,partial_quota,other_quota,context]
        val _ = print ("SUSPENSION_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "conjunct suspension retains sibling names and allowances";
         if rewrite_suspension_fixture () then OK ()
         else die "conjunct suspension lost history, siblings or controls");

(* Invocation fragment removal preserves the sources' consumed counters. *)
fun control_replay_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "controlReplayFixture"
        val g = new_definition ("rep_g_def", ``rep_g (x:bool) = T``)
        val h = new_definition ("rep_h_def", ``rep_h (x:bool) = T``)
        val c = new_definition ("rep_c_def", ``rep_c (x:bool) = T``)
        val k = new_definition ("rep_k_def", ``rep_k (x:bool) = T``)
        val u = new_definition ("rep_u_def", ``rep_u (x:bool) = T``)
        fun proof tm = Tactical.prove (tm,REWRITE_TAC [g,h,c,k,u])
        val original = proof ``!x. rep_c (rep_g x) = rep_k x``
        val reducer = proof ``!x. rep_g x = rep_h x``
        val unrelated = proof ``!x. rep_u x = rep_k x``
        val x = ``x:bool``
        val view = GEN x (TRANS
          (SYM (AP_TERM ``rep_c`` (SPEC x reducer))) (SPEC x original))
        val name = {Thy=current_theory (),Name="replay_source"}
        fun source ss = valOf (List.find
          (fn source => #1 (source_rewrite source) = SOME
            {Thy=current_theory (),Name="replay_source.1"})
          (rewrite_source_handles ss))
        val dummy = name_ss "replay dummy" (rewrites [unrelated])
        fun installed th =
          let val ss = pureSimps.pure_ss ++ dummy ++
                name_ss "replay originals" (rewrites_with_names [(name,th)])
          in ss ++ name_ss "replay views" (rewrite_views [(source ss,view)]) end
        val tm = ``rep_c (rep_g x)``
        val vtm = ``rep_c (rep_h x)``
        val result = ``rep_k x``
        fun converted ss input expected =
          let val th = QCONV (SIMP_CONV ss []) input
          in null (hyp th) andalso aconv (rhs (concl th)) expected andalso
             null (valid (ACCEPT_TAC th) ([],mk_eq (input,expected))) end
        fun replay ss = remove_ssfrags_preserving_controls ["replay dummy"] ss
        val once = installed (Once original)
        val used = converted once tm result
        val exhausted = replay once
        val exhausted_quota = used andalso converted exhausted tm tm andalso
          converted exhausted vtm vtm
        val twice = installed (Ntimes original 2)
        val used_view = converted twice vtm result
        val partial = replay twice
        val shared = used_view andalso converted partial tm result andalso
          converted twice vtm vtm andalso converted partial vtm vtm
        val ordinary = remove_ssfrags ["replay dummy"] once
        val ordinary_unchanged = converted ordinary tm result
        val unbounded = replay (installed original)
        val unbounded_rules = converted unbounded tm result andalso
          converted unbounded vtm result
        val excluded_th = QCONV
          (SIMP_CONV unbounded [Excl "replay_source"]) vtm
        val excluded = null (hyp excluded_th) andalso
          aconv (rhs (concl excluded_th)) vtm andalso
          null (valid (ACCEPT_TAC excluded_th) ([],mk_eq (vtm,vtm)))
        val identity = same_rewrite_source (source once,source exhausted)
        val missing = ((ignore
          (remove_ssfrags_preserving_controls ["missing"] once); false)
          handle UNCHANGED => true)
        val bundle = prepare_rewrite_bundle pureSimps.pure_ss [Once original]
        val bundle_source = hd (#2 (hd (rewrite_bundle_rules bundle)))
        val prepared = install_rewrite_bundle bundle [(bundle_source,view)]
          (pureSimps.pure_ss ++ dummy)
        val prepared_used = converted prepared vtm result
        val prepared_replayed = replay prepared
        val prepared_quota = prepared_used andalso
          converted prepared_replayed tm tm andalso
          converted prepared_replayed vtm vtm
        val checks = [exhausted_quota,shared,ordinary_unchanged,unbounded_rules,
                      excluded,identity,missing,prepared_quota]
        val _ = print ("CONTROL_REPLAY_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "invocation fragment replay preserves consumed controls";
         if control_replay_fixture () then OK ()
         else die "invocation replay revived a source or its view");

(* Installed bindings keep source context and counters through global passes. *)
fun bound_global_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "boundGlobalFixture"
        val i = new_definition ("bg_i_def", ``bg_i (x:bool) = T``)
        val o_def = new_definition ("bg_o_def", ``bg_o (x:bool) = T``)
        val rule = Tactical.prove
          (``!x. bg_i x = bg_o x``,REWRITE_TAC [i,o_def])
        val sentinel = REFL ``bg_sentinel:bool``
        val input = ``bg_i x``
        val output = ``bg_o x``
        val cfg : xsimptac_config =
          {base={strip=false,elimvars=false,droptrues=false,oldestfirst=true},
           concl_in_fixpoint=true,imp_rebuild=true,imp_premises=true}
        val policy : Traverse.child_first_policy =
          {charge=fn () => (),keep_abstraction=K false}
        fun tactic ss bundle arguments =
          GEN_GLOBAL_SIMP_TAC_CHILD_FIRST_BOUND policy {safe=false}
            cfg ss bundle arguments
        fun checked tac goal =
          let
            val (goals,validation) = runtac (VALID tac) goal
            val proofs = map
              (fn residual => Tactical.prove_goal
                (residual,REWRITE_TAC [i,o_def,boolTheory.EXCLUDED_MIDDLE]))
              goals
            val theorem = validation proofs
            val _ = if aconv (concl theorem) (#2 goal) then ()
                    else raise Fail "bound global validation"
          in goals end
        fun same (left,right) = ListPair.allEq
          (fn ((asl,w),(bsl,v)) => aconv w v andalso
            ListPair.allEq (fn (a,b) => aconv a b) (asl,bsl)) (left,right)
        val compiles = ref 0
        val base = empty_ss ++ SSFRAG
          {name=NONE,convs=[],rewrs=[],ac=[],dprocs=[],congs=[],
           filter=SOME (fn th => (compiles := !compiles + 1; [th]))}
        val bundle = prepare_rewrite_bundle base [Once rule]
        val installed = install_rewrite_bundle bundle [] base
        val pass = tactic installed bundle []
        val first = same (checked pass ([],input),[([],output)])
        val second = same (checked pass ([],input),[([],input)])
        val compile_once = !compiles = 1
        val twice_bundle = prepare_rewrite_bundle empty_ss [Ntimes rule 2]
        val twice = tactic (install_rewrite_bundle twice_bundle [] empty_ss)
          twice_bundle []
        val partial = same (checked twice ([],input),[([],output)]) andalso
          same (checked twice ([],input),[([],output)]) andalso
          same (checked twice ([],input),[([],input)])
        val dummy = name_ss "bound global dummy" (rewrites [sentinel])
        val marker_base = empty_ss ++ dummy
        val marker_bundle = prepare_rewrite_bundle marker_base [Once rule]
        val marker_ss = install_rewrite_bundle marker_bundle [] marker_base
        val consumed = QCONV (SIMP_CONV marker_ss []) input
        val marker = concl (ExclSF "bound global dummy")
        val marker_goal = ([marker],input)
        val exhausted = aconv (rhs (concl consumed)) output andalso
          same (checked (tactic marker_ss marker_bundle []) marker_goal,
                [marker_goal])
        val condition = SPEC ``bg_p:bool`` boolTheory.EXCLUDED_MIDDLE
        val condition_tm = concl condition
        val conditional = DISCH condition_tm
          (EQT_INTRO (ASSUME condition_tm))
        val solver_calls = ref 0
        val untagged = ref true
        fun solver {context_thms,...} tm =
          let
            val found = List.filter
              (fn th => aconv (concl th) (concl sentinel)) context_thms
            val _ = solver_calls := !solver_calls + 1
            val _ = untagged := (!untagged andalso
              List.all (not o can BoundedRewrites.DEST_BOUNDED) found)
          in
            if aconv tm condition_tm andalso not (null found) then condition
            else raise mk_HOL_ERR "boundGlobal" "solver" "missing context"
          end
        val solver_base = add_unsafe_solver
          {name="bound global context",solve=solver}
          (empty_ss ++ rewrites [conditional])
        val context_bundle = prepare_rewrite_bundle solver_base [Once sentinel]
        val context_ss = install_rewrite_bundle context_bundle [] solver_base
        val context_tac = tactic context_ss context_bundle []
        val deferred = !solver_calls = 0
        val context_result = null (checked context_tac
          ([condition_tm],condition_tm))
        val traversal_context = context_result andalso !solver_calls >= 2
          andalso !untagged
        val final_base = add_unsafe_solver
          {name="bound final context",solve=solver} empty_ss
        val final_bundle = prepare_rewrite_bundle final_base [Once sentinel]
        val final_ss = install_rewrite_bundle final_bundle [] final_base
        val final_context = null (checked (tactic final_ss final_bundle [])
          ([],condition_tm))
        val root_rule = DISCH condition_tm (Tactical.prove
          (``(bg_i x ==> bg_i y) = (bg_o x ==> bg_o y)``,
           REWRITE_TAC [i,o_def]))
        val root_base = add_unsafe_solver
          {name="bound root context",solve=solver}
          (empty_ss ++ rewrites [root_rule])
        val root_bundle = prepare_rewrite_bundle root_base [Once sentinel]
        val root_ss = install_rewrite_bundle root_bundle [] root_base
        val root_first = same
          (checked (tactic root_ss root_bundle [])
            ([],``bg_i x ==> bg_i y``),
           [([``bg_o x``],``bg_o y``)])
        val rebuild_bundle = prepare_rewrite_bundle root_base [Once sentinel]
        val rebuild_ss = install_rewrite_bundle rebuild_bundle [] root_base
        val rebuild_context = same
          (checked (tactic rebuild_ss rebuild_bundle [])
            ([``bg_i x``],``bg_i y``),
           [([``bg_o x``],``bg_o y``)])
        val marker_source = hd (#2 (hd (rewrite_bundle_rules marker_bundle)))
        val marker_views = marker_ss ++ name_ss "bound global views"
          (rewrite_views [(marker_source,rule)])
        val view_controls = same
          (checked (tactic marker_views marker_bundle []) marker_goal,
           [marker_goal])
        val empty_bundle = prepare_rewrite_bundle pureSimps.pure_ss []
        val empty_bound = install_rewrite_bundle empty_bundle []
          pureSimps.pure_ss
        val _ = new_constant ("bg_context_p",bool)
        val context_goal = ([``bg_context_p``],``bg_i bg_context_p``)
        val ordinary_context = same
          (checked (tactic empty_bound empty_bundle []) context_goal,
           [([``bg_context_p``],``bg_i T``)])
        val no_context = same
          (checked (tactic empty_bound empty_bundle [markerLib.NoAsms])
            context_goal,[context_goal])
        val ignored_context = same
          (checked (tactic empty_bound empty_bundle
            [markerLib.IgnAsm `bg_context_p`]) context_goal,[context_goal])
        val checks = [first,second,compile_once,partial,exhausted,deferred,
                      traversal_context,final_context,root_first,
                      rebuild_context,view_controls,ordinary_context,
                      no_context,ignored_context]
        val _ = print ("BOUND_GLOBAL_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "bound global passes retain source context and controls";
         if bound_global_fixture () then OK ()
         else die "bound global pass lost context or revived controls");

(* Argument controls precede binding without reviving surviving occurrences. *)
fun bound_arguments_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "boundArgumentsFixture"
        val i = new_definition ("ba_i_def", ``ba_i (x:bool) = T``)
        val o_def = new_definition ("ba_o_def", ``ba_o (x:bool) = T``)
        val rule = Tactical.prove
          (``!x. ba_i x = ba_o x``,REWRITE_TAC [i,o_def])
        val input = ``ba_i x``
        val output = ``ba_o x``
        val name = {Thy=Theory.current_theory (),Name="survivor"}
        fun base () = pureSimps.pure_ss ++ name_ss "bound argument survivor"
          (rewrites_with_names [(name,Ntimes rule 2)]) ++
          name_ss "bound argument dummy" (rewrites [REFL ``ba_sentinel:bool``])
        fun result ss = rhs (concl (QCONV (SIMP_CONV ss []) input))
        val ordinary = base ()
        val bounded = Once rule
        val (unchanged,originals) = prepare_rewrite_arguments ordinary
          [bounded]
        val identity = Portable.pointer_eq (ordinary,unchanged) andalso
          (case originals of [theorem] => Portable.pointer_eq (theorem,bounded)
           | _ => false)
        val first = result ordinary
        val (prepared,rest) = prepare_rewrite_arguments ordinary
          [ExclSF "bound argument dummy",Once rule]
        val partial = aconv first output andalso aconv (result prepared) output
          andalso aconv (result prepared) input
          andalso aconv (result ordinary) input
        val tags = case rest of [theorem] =>
          let val (payload,uses) = BoundedRewrites.DEST_BOUNDED theorem
          in uses = 1 andalso aconv (concl payload) (concl rule)
             andalso null (hyp payload) end
          | _ => false
        val exhausted = base ()
        val _ = result exhausted
        val _ = result exhausted
        val (after_exhaustion,_) = prepare_rewrite_arguments exhausted
          [ExclSF "bound argument dummy"]
        val no_revival = aconv (result after_exhaustion) input
        val (excluded,_) = prepare_rewrite_arguments (base ())
          [ExclX "rule:boundArgumentsFixture.survivor"]
        val exclusion = aconv (result excluded) input
        val (with_fragment,_) = prepare_rewrite_arguments excluded
          [SF (name_ss "bound argument added" (rewrites [rule]))]
        val addition = aconv (result with_fragment) output
        val checks = [identity,partial,tags,no_revival,exclusion,addition]
        val _ = print ("BOUND_ARGUMENT_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "argument preparation retains surviving rewrite controls";
         if bound_arguments_fixture () then OK ()
         else die "argument preparation revives rewrite controls");

(* History edits must reuse an invocation's already compiled originals. *)
fun prepared_replay_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "preparedReplayFixture"
        val i = new_definition ("pr_i_def", ``pr_i (x:bool) = T``)
        val h = new_definition ("pr_h_def", ``pr_h (x:bool) = T``)
        val o_def = new_definition ("pr_o_def", ``pr_o (x:bool) = T``)
        val a = new_definition ("pr_a_def", ``pr_a (x:bool) = T``)
        val b = new_definition ("pr_b_def", ``pr_b (x:bool) = T``)
        fun proof tm = Tactical.prove
          (tm,REWRITE_TAC [i,h,o_def,a,b])
        val original = proof ``!x. pr_i x = pr_o x``
        val view = proof ``!x. pr_h x = pr_o x``
        val sibling = proof ``!x. pr_a x = pr_b x``
        val compiles = ref 0
        val dummy = name_ss "prepared replay dummy"
          (rewrites [REFL ``pr_sentinel:bool``])
        val base = pureSimps.pure_ss ++ dummy ++ SSFRAG
          {name=NONE,convs=[],rewrs=[],ac=[],dprocs=[],congs=[],
           filter=SOME (fn th => (compiles := !compiles + 1; [th]))}
        val bundle = prepare_rewrite_bundle base
          [Ntimes original 2,Once sibling]
        val rules = rewrite_bundle_rules bundle
        val first = hd (#2 (hd rules))
        val second = hd (#2 (List.nth (rules,1)))
        val installed = install_rewrite_bundle bundle [(first,view)] base
        fun result ss tm =
          let
            val (goals,validation) = runtac
              (VALID (CONV_TAC (QCONV (SIMP_CONV ss [])))) ([],tm)
            val proofs = map (fn goal => Tactical.prove_goal
              (goal,REWRITE_TAC [i,h,o_def,a,b])) goals
            val theorem = validation proofs
            val _ = if null (hyp theorem) andalso aconv (concl theorem) tm
                    then () else raise Fail "prepared replay validation"
          in
            case goals of
                [([],target)] => target
              | [] => T
              | _ => raise Fail "prepared replay residual"
          end
        val input = ``pr_i x``
        val alias = ``pr_h x``
        val output = ``pr_o x``
        val compiled = !compiles = 2
        val consumed = aconv (result installed input) output
        val replayed = remove_ssfrags_preserving_controls
          ["prepared replay dummy"] installed
        val reused = !compiles = 2
        val shared = aconv (result replayed alias) output andalso
          aconv (result replayed input) input andalso
          aconv (result installed alias) alias
        val masked = suspend_rewrite_sources [second] replayed
        val mask_cached = !compiles = 2
        val mask_exact = aconv (result masked ``pr_a x``) ``pr_a x`` andalso
          aconv (result masked input) input
        val (excluded,_) = prepare_rewrite_arguments replayed
          [ExclSF "missing prepared replay fragment"]
        val marker_cached = !compiles = 2
        val no_revival = aconv (result excluded input) input
        val filtered = filter_rewrites
          (fn (_,th) => not (can (find_term (aconv ``pr_i``)) (concl th)))
          replayed
        val filter_cached = !compiles = 2
        val filter_exact = not (List.exists
          (fn source => same_rewrite_source (source,first))
          (rewrite_source_handles filtered)) andalso
          List.exists (fn source => same_rewrite_source (source,second))
            (rewrite_source_handles filtered) andalso
          aconv (result filtered alias) alias andalso
          aconv (result filtered ``pr_a x``) ``pr_b x``
        val ordinary = remove_ssfrags
          ["prepared replay dummy"] installed
        val ordinary_controls = aconv (result ordinary input) output andalso
          aconv (result ordinary alias) output andalso
          aconv (result ordinary input) input
        val conjoined = prepare_rewrite_bundle base
          [Ntimes (CONJ original sibling) 2]
        val conjoined_compiles = !compiles
        val conjunction = install_rewrite_bundle conjoined [] base
        val _ = result conjunction input
        val _ = result conjunction ``pr_a x``
        val fresh_conjunction = remove_ssfrags
          ["prepared replay dummy"] conjunction
        val conjunction_uses = aconv (result fresh_conjunction input) output
          andalso aconv (result fresh_conjunction ``pr_a x``) ``pr_b x``
          andalso aconv (result fresh_conjunction input) input
          andalso aconv (result fresh_conjunction ``pr_a x``) ``pr_a x``
        val conjunction_cached = !compiles = conjoined_compiles
        val checks = [compiled,consumed,reused,shared,mask_cached,mask_exact,
                      marker_cached,no_revival,filter_cached,filter_exact,
                      ordinary_controls,conjunction_uses,conjunction_cached]
        val _ = print ("PREPARED_REPLAY_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "prepared originals survive history edits without compilation";
         if prepared_replay_fixture () then OK ()
         else die "history replay recompiles a prepared original bundle");

(* Rule transport filters its own citation without refreshing survivors. *)
fun bound_filter_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "boundFilterFixture"
        val i = new_definition ("bf_i_def", ``bf_i (x:bool) = T``)
        val h = new_definition ("bf_h_def", ``bf_h (x:bool) = T``)
        val o_def = new_definition ("bf_o_def", ``bf_o (x:bool) = T``)
        val a = new_definition ("bf_a_def", ``bf_a (x:bool) = T``)
        val b = new_definition ("bf_b_def", ``bf_b (x:bool) = T``)
        fun proof tm = Tactical.prove
          (tm,REWRITE_TAC [i,h,o_def,a,b])
        val rule = proof ``!x. bf_i x = bf_o x``
        val alias = proof ``!x. bf_h x = bf_o x``
        val removed_rule = proof ``!x. bf_a x = bf_b x``
        val compiles = ref 0
        val base = pureSimps.pure_ss ++ SSFRAG
          {name=NONE,convs=[],rewrs=[],ac=[],dprocs=[],congs=[],
           filter=SOME (fn th => (compiles := !compiles + 1; [th]))}
        val bundle = prepare_rewrite_bundle base
          [Ntimes rule 2,Once removed_rule]
        val source = hd (#2 (hd (rewrite_bundle_rules bundle)))
        val installed = install_rewrite_bundle bundle [(source,alias)] base
        fun result ss tm =
          let
            val (goals,validate) = runtac
              (VALID (CONV_TAC (QCONV (SIMP_CONV ss [])))) ([],tm)
            val theorem = validate (map (fn goal => Tactical.prove_goal
              (goal,REWRITE_TAC [i,h,o_def,a,b])) goals)
            val _ = if null (hyp theorem) andalso aconv (concl theorem) tm
                    then () else raise Fail "bound filter validation"
          in case goals of [([],target)] => target | [] => T
               | _ => raise Fail "bound filter residual" end
        fun keep (_,th) = not (can (find_term (aconv ``bf_a``)) (concl th))
        val input = ``bf_i x``
        val view_input = ``bf_h x``
        val output = ``bf_o x``
        val consumed = aconv (result installed input) output
        val filtered = filter_rewrites_preserving_controls keep installed
        val compile_once = !compiles = 2
        val partial = aconv (result filtered view_input) output
        val exhausted = aconv (result filtered input) input andalso
          aconv (result installed view_input) view_input
        val exact = aconv (result filtered ``bf_a x``) ``bf_a x``
        val unchanged = filter_rewrites_preserving_controls (K true) filtered
        val identity = Portable.pointer_eq (unchanged,filtered)
        val ordinary = filter_rewrites keep installed
        val ordinary_reset = aconv (result ordinary input) output andalso
          aconv (result ordinary view_input) output andalso
          aconv (result ordinary input) input
        val ambient = pureSimps.pure_ss ++ rewrites [Ntimes rule 2]
        val ambient_with_self = ambient ++ rewrites [removed_rule]
        val _ = result ambient_with_self input
        val ambient_filtered = filter_rewrites_preserving_controls
          keep ambient_with_self
        val ambient_shared = aconv (result ambient_filtered input) output
          andalso aconv (result ambient_filtered input) input
          andalso aconv (result ambient_with_self input) input
        val checks = [consumed,compile_once,partial,exhausted,exact,identity,
                      ordinary_reset,ambient_shared]
        val _ = print ("BOUND_FILTER_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "invocation filtering retains supplied and ambient quotas";
         if bound_filter_fixture () then OK ()
         else die "invocation filtering refreshes surviving rewrite quotas");

(* Combining bundles preserves consumed counters, events and aliases. *)
fun combined_bundle_fixture () =
  let
    val saved = Context.snapshot ()
    fun run () =
      let
        val _ = new_theory "combinedBundleFixture"
        val a = new_definition ("cb_a_def", ``cb_a (x:bool) = T``)
        val b = new_definition ("cb_b_def", ``cb_b (x:bool) = T``)
        val c = new_definition ("cb_c_def", ``cb_c (x:bool) = T``)
        val d = new_definition ("cb_d_def", ``cb_d (x:bool) = T``)
        val e = new_definition ("cb_e_def", ``cb_e (x:bool) = T``)
        fun proof tm = Tactical.prove (tm,REWRITE_TAC [a,b,c,d,e])
        val first = proof ``!x. cb_a x = cb_b x``
        val second = proof ``!x. cb_c x = cb_d x``
        val alias = proof ``!x. cb_e x = cb_b x``
        val compiles = ref 0
        val base = pureSimps.pure_ss ++ SSFRAG
          {name=NONE,convs=[],rewrs=[],ac=[],dprocs=[],congs=[],
           filter=SOME (fn th => (compiles := !compiles + 1; [th]))}
        val one = prepare_rewrite_bundle base [Ntimes first 2]
        val two = prepare_rewrite_bundle base [Once second]
        val source = hd (#2 (hd (rewrite_bundle_rules one)))
        val original = install_rewrite_bundle one [] base
        fun result ss tm =
          let
            val (goals,validate) = runtac
              (VALID (CONV_TAC (QCONV (SIMP_CONV ss [])))) ([],tm)
            val theorem = validate (map (fn goal => Tactical.prove_goal
              (goal,REWRITE_TAC [a,b,c,d,e])) goals)
            val _ = if null (hyp theorem) andalso aconv (concl theorem) tm
                    then () else raise Fail "combined bundle validation"
          in case goals of [([],target)] => target | [] => T
               | _ => raise Fail "combined bundle residual" end
        val partial = aconv (result original ``cb_a x``) ``cb_b x``
        val combined = combine_rewrite_bundles [one,two]
        val groups = rewrite_bundle_rules combined
        val same_source = same_rewrite_source
          (source,hd (#2 (hd groups))) andalso length groups = 2
        val installed = install_rewrite_bundle combined [(source,alias)] base
        val alias_used = aconv (result installed ``cb_e x``) ``cb_b x``
        val exhausted = aconv (result original ``cb_a x``) ``cb_a x``
          andalso aconv (result installed ``cb_a x``) ``cb_a x``
        val other_used = aconv (result installed ``cb_c x``) ``cb_d x``
          andalso aconv (result installed ``cb_c x``) ``cb_c x``
        val duplicate = (ignore (combine_rewrite_bundles [one,one]); false)
          handle HOL_ERR _ => true
        val reinstall =
          (ignore (install_rewrite_bundle combined [] original); false)
          handle HOL_ERR _ => true
        val cached = !compiles = 2
        val checks = [partial,same_source,alias_used,exhausted,other_used,
                      duplicate,reinstall,cached]
        val _ = print ("COMBINED_BUNDLE_RESULTS " ^
          String.concatWith " " (map Bool.toString checks) ^ "\n")
      in List.all I checks end
  in Portable.finally (fn () => Context.restore saved) run () end;

val _ = (tprint "combined bundles retain sources and actual rewrite quotas";
         if combined_bundle_fixture () then OK ()
         else die "combining bundles refreshes a quota or loses an origin");

(* Rebuilding a solver list does not change its ordered solver identities. *)
val _ =
  let
    val first = mk_tactic_solver ("context_first", Tactical.NO_TAC)
    val second = mk_tactic_solver ("context_second", Tactical.NO_TAC)
    fun configured () = set_unsafe_solvers [first] empty_ss
    val original = configured ()
    val equivalent = configured ()
    val changed = set_unsafe_solvers [second] original
    val removed = set_unsafe_solvers [] original
    val reordered = set_unsafe_solvers [second,first] original
    val reverse = set_unsafe_solvers [first,second] original
    fun rebuild next = #rebuild (rewrite_context_changes (original,next))
    val checks =
      [not (rebuild original),not (rebuild equivalent),rebuild changed,
       rebuild removed,
       #rebuild (rewrite_context_changes (reordered,reverse))]
    val _ = print ("SOLVER_CONTEXT_RESULTS " ^
      String.concatWith " " (map Bool.toString checks) ^ "\n")
  in
    tprint "rewrite context compares ordered solver identities";
    if List.all I checks then OK ()
    else die "solver context identity, removal or order is incorrect"
  end

(* ---------------------------------------------------------------------- *)
(* R2: reusable legacy contexts versus explicit extended-engine refresh.   *)
(* These lifetime goldens distinguish construction from application;       *)
(* single-use conversions cannot detect this difference.                  *)
(* ---------------------------------------------------------------------- *)
local
  exception R2_CONTEXT
  val atom = ``r2_context_p:bool``
  val input = ``T /\ r2_context_p``
  val once = BoundedRewrites.Once
    (CONJUNCT1 (SPEC atom boolTheory.AND_CLAUSES))
  val cong_qconv =
    congLib.CONGRUENCE_SIMP_QCONV boolSyntax.equality
      (congLib.mk_congset [])
  val legacy_builders =
    [("TRAVERSE",fn ss => Traverse.TRAVERSE (traversedata_for_ss ss)),
     (* Tracked projection is total: directly replace the old valOf route,
        without reconstructing a set or changing collector lifetimes. *)
     ("TRAVERSE native projection",fn ss =>
        Traverse.TRAVERSE (traversedata_for_ss ss)),
     ("CONGRUENCE_SIMP_QCONV",cong_qconv)]

  (* An atomic input avoids congruence-generated context additions. *)
  fun lifetime_reducer lift name build expected =
    let
      val calls = ref 0
      val reducer = lift (lifted_reducer
        {name=SOME "R2 context callback",initial=R2_CONTEXT,
         addcontext=fn (ctxt,_) => (calls := !calls + 1; ctxt),
         apply=fn _ => NO_CONV})
      val ss = pureSimps.pure_ss ++ dproc_ss reducer
      val cv = build ss [boolTheory.TRUTH]
      val constructed = !calls
      val _ = QCONV (TRY_CONV cv) atom
      val first = !calls
      val _ = QCONV (TRY_CONV cv) atom
    in
      tprint ("context lifetime: " ^ name);
      if [constructed,first,!calls] = expected then OK ()
      else die "initial context callback ran at the wrong time"
    end

  fun lifetime name build expected =
    lifetime_reducer I name build expected

  fun contextual reducer =
    Traverse.CONTEXT_REDUCER (Traverse.reducer_data reducer)
  fun configured reducer =
    Traverse.CONFIG_REDUCER (Traverse.reducer_config_data reducer)

  fun once_lifetime name build refresh =
    let
      val cv = QCONV (TRY_CONV (build pureSimps.pure_ss [once]))
    in
      convtest (name ^ ": reusable Once first application",cv,input,atom);
      convtest (name ^ ": reusable Once second application",cv,input,
                if refresh then atom else input);
      convtest (name ^ ": new construction decodes a fresh Once",
                QCONV (TRY_CONV (build pureSimps.pure_ss [once])),
                input,atom)
    end

  val rejecting_solver : Traverse.ssolver =
    {name="R2 rejecting solver",solve=fn _ => fn tm => NO_CONV tm}
  val conversion_settings =
    [("subgoaler",set_subgoaler (fn _ => REFL)),
     ("unsafe solver",set_unsafe_solvers [rejecting_solver]),
     ("condition depth",set_cond_depth 4),
     ("term order",set_term_ord Cond_rewr.ac_term_ord)]
  val tactic_settings =
    [("safe solver",set_safe_solvers [rejecting_solver]),
     ("looper",set_looper ("R2 unused looper",K ALL_TAC))]
in
  val _ = List.app
    (fn (name,build) => lifetime name build [1,1,1]) legacy_builders
  val _ = List.app
    (fn (name,build) => once_lifetime name build false)
    (List.take (legacy_builders,2))

  (* Context/config procedures in tracked default projections keep the
     construction-time collectors, not XTRAVERSE refresh. The old ordinary
     optional getter rejected these types; no such getter is used here. *)
  val _ = List.app
    (fn (kind,lift) => List.app
      (fn (name,build) =>
        lifetime_reducer lift (name ^ " + " ^ kind) build [1,1,1])
      [("TRAVERSE mixed",fn ss =>
          Traverse.TRAVERSE (traversedata_for_ss ss)),
       ("CONGRUENCE_SIMP_QCONV mixed",cong_qconv)])
    [("contextual",contextual),("configured",configured)]

  (* The ordinary total wrappers deliberately construct their QCONV
     inside tm. Do not move their construction ahead of tm. *)
  val _ = lifetime "SIMP_CONV (ordinary delayed wrapper)"
    SIMP_CONV [0,1,2]
  val _ = lifetime "CONGRUENCE_SIMP_CONV (ordinary delayed wrapper)"
    (congLib.CONGRUENCE_SIMP_CONV boolSyntax.equality
       (congLib.mk_congset [])) [0,1,2]

  (* Explicit extended APIs refresh even at the unconfigured settings. *)
  val _ = lifetime "XTRAVERSE with default_config"
    (fn ss => Traverse.XTRAVERSE
       (traversedata_for_ss ss,Traverse.default_config)) [0,1,2]
  val _ = lifetime "TRAVERSE_WITH_CONTEXT with default_config"
    (fn ss => fn ths => Traverse.TRAVERSE_WITH_CONTEXT Traverse.ParentFirst
       (traversedata_for_ss ss,Traverse.default_config)
       {reducer_context=ths,solver_context=[]}) [0,1,2]
  val _ = lifetime "ROOT_REWRITE with default_config"
    (fn ss => Traverse.ROOT_REWRITE
       (traversedata_for_ss ss,Traverse.default_config)) [0,1,2]
  val _ = once_lifetime "XTRAVERSE with default_config"
    (fn ss => Traverse.XTRAVERSE
       (traversedata_for_ss ss,Traverse.default_config)) true

  (* Conversions consume these four settings, but not safe solvers/loopers.
     Merely storing a tactic-only setting must not opt a QCONV into refresh. *)
  val _ = List.app
    (fn (setting,configure) => List.app
      (fn (name,build) =>
        lifetime (name ^ " + " ^ setting) (build o configure) [0,1,2])
      [("CONGRUENCE_SIMP_QCONV",cong_qconv)])
    conversion_settings
  val _ = List.app
    (fn (setting,configure) => List.app
      (fn (name,build) =>
        lifetime (name ^ " + " ^ setting) (build o configure) [1,1,1])
      [("CONGRUENCE_SIMP_QCONV",cong_qconv)])
    tactic_settings
end

(* R4: FRAG lookup and dispatch wait for the goal's current Context.
   Run the same assertions in both typed registries; restore each Context. *)
local
  fun registry_tests prefix builders register = let
    val atom = ``r4_fragment_p:bool``
    val goal = ([],``T /\ r4_fragment_p``)
    val expected = [([],atom)]
    val rule = CONJUNCT1 (SPEC atom boolTheory.AND_CLAUSES)
    fun pin msg constructed =
      (tprint (prefix ^ msg);
       require_msg
         (fn Exn.Res (sgs,_) => list_eq goal_eq expected sgs | _ => false)
         (K "saved tactic did not use the application-time fragment")
         (fn () => runtac (VALID (Exn.release constructed)) goal) ())

    fun delayed (label,build) = let
      val saved = Context.snapshot ()
      fun run () = let
        val name = "r4_late_registration_" ^ label
        val constructed = Exn.capture build [markerLib.FRAG name]
        val _ = register (name,[rule])
      in
        pin ("R4 delayed FRAG registration: " ^ label) constructed
      end
    in Portable.finally (fn () => Context.restore saved) run () end

    fun contexts (label,build) = let
      val absent = Context.snapshot ()
      fun run () = let
        val name = "r4_context_registration_" ^ label
        val directive = markerLib.FRAG name
        val _ = register (name,[rule])
        val present = Context.snapshot ()
        val constructed = Exn.capture build [directive]
        val _ = Context.restore absent
        val _ = tprint (prefix ^
          "R4 saved tactic sees absent Context: " ^ label)
        val _ = require_msg
          (fn Exn.Exn (HOL_ERR e) =>
                String.isSubstring ("No frag called " ^ name)
                  (Feedback.message_of e)
            | _ => false)
          (K "missing fragment must fail at application, not construction")
          (fn () => runtac (VALID (Exn.release constructed)) goal) ()
        val from_absent = Exn.capture build [directive]
        val _ = Context.restore present
        val _ = pin ("R4 saved tactic sees restored Context: " ^ label)
          constructed
      in
        pin ("R4 tactic constructed in absent Context: " ^ label) from_absent
      end
    in Portable.finally (fn () => Context.restore absent) run () end
  in
    List.app delayed builders;
    List.app contexts builders
  end
  val cfg = {strip=false,elimvars=false,droptrues=false,oldestfirst=true}
in
  val _ = let
    open OrdinarySimp
  in
    registry_tests ""
      [("ASM_SIMP_TAC",ASM_SIMP_TAC empty_ss),
       ("SIMP_TAC",SIMP_TAC empty_ss),
       ("global_simp_tac",global_simp_tac cfg empty_ss)]
      (fn (name,rules) => ignore (register_frag
        (name_ss name (rewrites rules))))
  end
  val _ = registry_tests "extension registry: "
    [("ASM_SIMP_TAC",ASM_SIMP_TAC empty_ss),
     ("SIMP_TAC",SIMP_TAC empty_ss),
     ("global_simp_tac",global_simp_tac cfg empty_ss)]
    (fn (name,rules) => ignore (register_frag
      (name_ss name (rewrites rules))))
end

(* ++ rejects a malformed bounded tag before any public filter callback,
   and runs all makers before conversion/trace callbacks. *)
local
  exception SCHEDULE_FILTER
  val rule = CONJUNCT1
    (SPEC ``schedule_p:bool`` boolTheory.AND_CLAUSES)
  val malformed = ADD_ASSUM
    (mk_comb (boolSyntax.bounded_tm,mk_var ("not_a_number",bool))) rule
  fun frag filter ac rewrs =
    SSFRAG {name=NONE,congs=[],convs=[],rewrs=map (pair NONE) rewrs,ac=ac,
            filter=filter,dprocs=[]}

  fun malformed_order (name,ac,rewrs,throws) =
    let
      val calls = ref 0
      fun maker rw =
        (calls := !calls + 1;
         if throws then raise SCHEDULE_FILTER else [rw])
      val ss = empty_ss ++ frag (SOME maker) [] []
      val result = Exn.capture (fn () => ss ++ frag NONE ac rewrs) ()
      val correct =
        case result of Exn.Exn Option => !calls = 0 | _ => false
    in
      tprint ("++ malformed tag precedes filter: " ^ name);
      if correct then OK ()
      else die "filter ran before all ordinary bounded tags were decoded"
    end

  fun staged_order (name,ac,rewrs,count) =
    let
      val events = ref ([] : string list)
      fun record event = events := event :: !events
      fun maker rw = (record "maker"; [rw])
      val ss = empty_ss ++ frag (SOME maker) [] []
      val listener = "++ staged compilation parity"
      fun watch (2,Trace.LZ_TEXT text) =
            if String.isPrefix "New rewrite: " (text ()) then
              record "convert"
            else ()
        | watch _ = ()
      val _ = Listener.add_listener Trace.trace_hook (listener,watch)
      val _ = Portable.finally
        (fn () => ignore (Listener.remove_listener Trace.trace_hook listener))
        (fn () => ignore (ss ++ frag NONE ac rewrs)) ()
      val expected = List.tabulate (count,K "maker") @
                     List.tabulate (count,K "convert")
    in
      tprint ("++ all makers precede conversions: " ^ name);
      if List.rev (!events) = expected then OK ()
      else die "rewrite-maker and conversion callbacks were interleaved"
    end
in
  val _ = List.app malformed_order
    [("ordinary/effect",[],[rule,malformed],false),
     ("ordinary/exception",[],[rule,malformed],true),
     ("AC/effect",[(CONJ_COMM,CONJ_ASSOC)],[malformed],false),
     ("AC/exception",[(CONJ_COMM,CONJ_ASSOC)],[malformed],true)]
  val _ = List.app staged_order
    [("ordinary",[],[rule,rule],2),
     ("AC and ordinary",[(CONJ_COMM,CONJ_ASSOC)],[rule,rule],5)]
end

(* R6 legacy congruence-factory scheduling; baseline-only APIs. *)
val _ = let
  val a = ``r6_a:bool``
  val b = ``r6_b:bool``
  val c = ``r6_c:bool``
  val ab = ASSUME (boolSyntax.mk_eq (a,b))
  val bc = ASSUME (boolSyntax.mk_eq (b,c))
  exception R6Context
  exception R6RootStop
  fun label tm =
    if aconv tm a then "a"
    else if aconv tm b then "b"
    else if aconv tm c then "c"
    else "other"
  fun record log s = log := s :: !log
  fun events log = List.rev (!log)
  fun check name condition =
    (tprint name;
     if condition then OK () else die "R6 baseline schedule mismatch")
  fun reducer action =
    OrdinaryTraverse.REDUCER
      {name=NONE, initial=R6Context,
       addcontext=fn (ctxt,_) => ctxt,
       apply=fn {solver,conv,context,stack,relation} => action}
  fun failing_factory log tag : Opening.congproc =
    fn _ =>
      (record log ("relation-" ^ tag);
       fn {solver,freevars,depther} =>
         (record log ("factory-" ^ tag);
          fn tm => (record log (tag ^ ":" ^ label tm); NO_CONV tm)))
  fun make rewriters dprocs congprocs weakenprocs =
    OrdinaryTraverse.TRAVERSE
      {rewriters=rewriters, dprocs=dprocs, limit=NONE,
       relation=boolSyntax.equality,
       travrules=Travrules.TRAVRULES
         {relations=[Travrules.EQ_preorder],
          congprocs=congprocs, weakenprocs=weakenprocs}} []
  fun proves th left right =
    aconv (lhs (concl th)) left andalso aconv (rhs (concl th)) right

  (* Context factories must precede even the first root reducer. *)
  val order_log = ref ([] : string list)
  val root_reducer = reducer (fn tm =>
    (record order_log ("R:" ^ label tm);
     if aconv tm a then ab else NO_CONV tm))
  val order_cv = make [root_reducer] []
    [failing_factory order_log "C"] [failing_factory order_log "W"]
  val _ = check "R6 factories are not run when TRAVERSE is constructed"
    (null (!order_log))
  val order_th = order_cv a
  val _ = check "R6 context factories precede root reducer attempts"
    (proves order_th a b andalso events order_log =
       ["relation-C", "relation-W", "factory-C", "factory-W",
        "R:a", "R:b", "C:b", "W:b"])

  (* loop revisits three roots without reconstructing trav_convs.
     Reusing the outer conversion, however, creates a fresh trav_convs. *)
  val retry_log = ref ([] : string list)
  val retry_reducer = reducer (fn tm =>
    (record retry_log ("D:" ^ label tm);
     if aconv tm a then ab
     else if aconv tm b then bc
     else NO_CONV tm))
  val retry_cv = make [] [retry_reducer]
    [failing_factory retry_log "C"] [failing_factory retry_log "W"]
  val retry_expected =
    ["relation-C", "relation-W", "factory-C", "factory-W",
     "C:a", "D:a", "C:b", "D:b", "C:c", "D:c", "W:c"]
  val retry_th1 = retry_cv a
  val _ = check "R6 one factory construction across three loop tries"
    (proves retry_th1 a c andalso events retry_log = retry_expected)
  val retry_th2 = retry_cv a
  val _ = check "R6 factories refresh once on conversion reuse"
    (proves retry_th2 a c andalso
     events retry_log = retry_expected @ retry_expected)

  (* A non-HOL_ERR from the root reducer prevents either conversion
     from being used. It is raised at term application, not in the
     reducer factory that mapfilter2 filters. *)
  val unused_log = ref ([] : string list)
  val stop_reducer = reducer (fn tm =>
    (record unused_log ("R:" ^ label tm); raise R6RootStop))
  val stop_cv = make [stop_reducer] []
    [failing_factory unused_log "C"] [failing_factory unused_log "W"]
  val stopped = (ignore (stop_cv a); false) handle R6RootStop => true
  val _ = check "R6 factories run even when root abort skips descent"
    (stopped andalso events unused_log =
      ["relation-C", "relation-W", "factory-C", "factory-W", "R:a"])

  (* A construction-time rejection is cached. Moving construction past
     the successful root rewrite changes the actual result theorem. *)
  val ready = ref false
  val gated_builds = ref 0
  val gated : Opening.congproc = fn _ =>
    fn {solver,freevars,depther} =>
      (gated_builds := !gated_builds + 1;
       if !ready then
         (fn tm => if aconv tm b then bc else NO_CONV tm)
       else raise mk_HOL_ERR "R6" "factory" "not ready")
  val enable_reducer = reducer (fn tm =>
    if aconv tm a then (ready := true; ab) else NO_CONV tm)
  val gated_cv = make [enable_reducer] [] [gated] []
  val gated_th = gated_cv a
  val _ = check "R6 factory rejection before root rewrite is retained"
    (proves gated_th a b andalso !ready andalso !gated_builds = 1)

  (* Explicit extended entries retain their lazy factory scheduling. *)
  val extended_log = ref ([] : string list)
  val extended_data =
    {rewriters=[T.lift (reducer (fn tm =>
       (record extended_log ("R:" ^ label tm);
        if aconv tm a then ab else NO_CONV tm)))],
     dprocs=[], limit=NONE, relation=boolSyntax.equality,
     travrules=Travrules.TRAVRULES
       {relations=[Travrules.EQ_preorder],
        congprocs=[failing_factory extended_log "C"],
        weakenprocs=[failing_factory extended_log "W"]}}
  val root_th = T.ROOT_REWRITE
    (extended_data,T.default_config) [] a
  val _ = check "R6 explicit root avoids unused context factories"
    (proves root_th a b andalso events extended_log =
       ["relation-C", "relation-W", "R:a"])
  val _ = extended_log := []
  val extended_th = T.XTRAVERSE
    (extended_data,T.default_config) [] a
  val _ = check "R6 explicit traversal retains lazy factory scheduling"
    (proves extended_th a b andalso events extended_log =
       ["relation-C", "relation-W", "R:a", "R:b",
        "factory-C", "C:b", "factory-W", "W:b"])
in
  ()
end

(* R7 baseline-only pins. Setup precedes hooks/meters; no new strategy API.
   Count.mk_meter leaves counting enabled, as with the existing Count pins. *)
local
  open OrdinarySimp
  val goal = ([],mk_var ("r7_goal",bool))
  val missing = markerSyntax.L "r7_nonexistent_label"
  val cong = markerLib.Cong boolTheory.LET_CONG
  fun bound name th = ADD_ASSUM
    (mk_comb (boolSyntax.bounded_tm,mk_var (name,bool))) th
  val badbound = bound "notanint" TRUTH
  val reqcong = markerLib.mk_Req0 cong
  val reqdcong = markerLib.mk_ReqD cong
  val mixed = markerLib.mk_Req0 (markerLib.mk_ReqD (bound "3" cong))
  val later = bound "~3" (bound "a_bad" TRUTH)
  val invalid_frag = ASSUME
    (mk_comb (inst [alpha |-> bool] (rator (concl (markerLib.FRAG "x"))),
              boolSyntax.T))
  val left = markerLib.FRAG "r7_missing_left"
  val right = markerLib.FRAG "r7_missing_right"

  fun error_has text result =
    case result of
        Exn.Exn (HOL_ERR e) =>
          String.isSubstring text (Feedback.message_of e)
      | _ => false
  val is_missing = error_has
    "No assumption with label r7_nonexistent_label"
  fun check label condition detail =
    (tprint label; if condition then OK () else die detail)

  fun with_hooks fmt out action = let
    val saved_mon = HOLFlags.get_bflag Rewrite.monitoring
    val saved_emit = !Feedback.emit_MESG
    val saved_fmt = !Feedback.MESG_to_string
    val saved_out = !Feedback.MESG_outstream
    fun restore () =
      (HOLFlags.set_bflag (Rewrite.monitoring, saved_mon);
       Feedback.emit_MESG := saved_emit;
       Feedback.MESG_to_string := saved_fmt;
       Feedback.MESG_outstream := saved_out)
    fun run () =
      (HOLFlags.set_bflag (Rewrite.monitoring, true);
       Feedback.emit_MESG := true;
       Feedback.MESG_to_string := fmt;
       Feedback.MESG_outstream := out;
       action ())
  in Portable.finally restore run () end

  fun messages label expected args = let
    val raw = ref ([] : string list)
    val out = ref ([] : string list)
    (* Saved tactic construction is also required to remain inert. *)
    val constructed = Exn.capture (SIMP_TAC empty_ss) args
    fun run () = let
      val result = Exn.capture
        (fn () => runtac (Exn.release constructed) goal) ()
    in
      check label
        (is_missing result andalso length (!raw) = expected andalso
         length (!out) = expected)
        ("wrong error/message count: formatter=" ^
         Int.toString (length (!raw)) ^ ", output=" ^
         Int.toString (length (!out)))
    end
  in
    with_hooks (fn s => (raw := s :: !raw; s))
      (fn s => out := s :: !out) run
  end

  exception R7SecondMessage
  fun throwing output = let
    val calls = ref 0
    fun bump () =
      (calls := !calls + 1;
       if !calls = 2 then raise R7SecondMessage else ())
    fun fmt s = (if output then () else bump (); s)
    fun out _ = if output then bump () else ()
    fun run () = let
      val result = Exn.capture
        (fn () => runtac (SIMP_TAC empty_ss [cong,missing]) goal) ()
    in
      check ("R7 second " ^ (if output then "output" else "formatter") ^
             " exception is not reached")
        (is_missing result andalso !calls = 1)
        "early marker decode reached the throwing hook"
    end
  in with_hooks fmt out run end

  fun counted action = let
    val meter = Count.mk_meter ()
    val result = Exn.capture action ()
  in (result,#prims (Count.read meter)) end

  fun decode_count label th = let
    (* Missing label stops before requirement stripping or simplification.
       Compare against exactly one isolated public classification attempt. *)
    val (_,one_decode) = counted (fn () => markerLib.dest_directive th)
    val (result,tactic_count) = counted
      (fn () => runtac (SIMP_TAC empty_ss [th,missing]) goal)
  in
    check label (is_missing result andalso one_decode > 0 andalso
                 tactic_count = one_decode)
      ("one decode=" ^ Int.toString one_decode ^
       ", tactic=" ^ Int.toString tactic_count)
  end

  fun stage label expected args =
    check label
      (error_has expected (Exn.capture
        (fn () => runtac (SIMP_TAC empty_ss args) goal) ()))
      "wrong old-stage error winner"

  (* Actual Cong rewrite monitor changes ordinary fragment Context before
     process_tags performs its own fresh lookup. No extension-only fields. *)
  fun context_case kind = let
    val saved = Context.snapshot ()
    val name = "r7_context_" ^ kind
    val atom = mk_var ("r7_context_p",bool)
    val gl = ([],mk_conj (boolSyntax.T,atom))
    val rule = CONJUNCT1 (SPEC atom boolTheory.AND_CLAUSES)
    val directive = markerLib.FRAG name
    val calls = ref 0
    fun run () = let
      val _ = register_frag (name_ss name (rewrites [rule]))
      val present = Context.snapshot ()
      val _ = Context.restore saved
      val _ = if kind = "change" then
                ignore (register_frag (name_ss name (rewrites [])))
              else if kind = "remove" then Context.restore present else ()
      fun fmt s =
        (calls := !calls + 1;
         if !calls = 1 then
           if kind = "register" then
             ignore (register_frag (name_ss name (rewrites [rule])))
           else if kind = "remove" then Context.restore saved
           else Context.restore present
         else ();
         s)
      val result = with_hooks fmt (K ())
        (fn () => Exn.capture
          (fn () => runtac (VALID (SIMP_TAC empty_ss [cong,directive])) gl)
          ())
      val correct =
        if kind = "remove" then error_has ("No frag called " ^ name) result
        else case result of
                 Exn.Res (sgs,_) => list_eq goal_eq [([],atom)] sgs
               | _ => false
    in
      check ("R7 Cong callback " ^ kind ^ " uses fresh old-stage FRAG")
        (correct andalso !calls > 0) "stale/early fragment lookup"
    end
  in Portable.finally (fn () => Context.restore saved) run () end
in
  val _ = messages "R7 Cong: preserve old formatter/output callbacks"
    1 [cong,missing]
  val _ = messages "R7 Req0 Cong: do not inspect wrapped payload early"
    0 [reqcong,missing]
  val _ = decode_count "R7 malformed bound: one old-stage decode only"
    badbound
  val _ = messages "R7 ReqD Cong: do not inspect wrapped payload early"
    0 [reqdcong,missing]
  val _ = messages "R7 mixed Req0/ReqD/bound Cong: no early payload"
    0 [mixed,missing]
  val _ = messages "R7 valid bound Cong: no early payload"
    0 [bound "2" cong,missing]
  val _ = messages "R7 malformed bound Cong: same conclusion head"
    1 [bound "notanint" cong,missing]
  val _ = messages "R7 AC: no early proof decoder"
    1 [markerLib.AC boolTheory.CONJ_COMM boolTheory.CONJ_ASSOC,missing]
  val _ = throwing false
  val _ = throwing true
  val _ = decode_count "R7 Req0: only old-stage discharge" reqcong
  val _ = decode_count "R7 ReqD: only old-stage discharge" reqdcong
  val _ = decode_count "R7 valid bound: only old-stage discharge"
    (bound "3" TRUTH)
  val _ = decode_count "R7 malformed first bound does not skip to later"
    later
  val _ = decode_count "R7 negative bound: preserve decoder policy"
    (bound "~2" TRUTH)
  val _ = decode_count "R7 numeric prefix bound: preserve decoder policy"
    (bound "2suffix" TRUTH)
  val _ = stage "R7 missing label precedes missing FRAG"
    "No assumption with label r7_nonexistent_label" [missing,left]
  val _ = stage "R7 Abbr pretactic precedes missing FRAG"
    "No assumption of the form" [markerSyntax.Abbr [QUOTE "r7_absent"],left]
  val _ = stage "R7 two missing FRAGs retain right-fold error ordering"
    "No frag called r7_missing_right" [left,right]
  val _ = messages "R7 non-variable FRAG is not a named lookup"
    0 [invalid_frag,missing]
  val _ = stage "R7 missing label precedes ExclX target resolution"
    "No assumption with label r7_nonexistent_label"
    [ExclX "rule:r7_missing_target",missing]
  val _ = stage "R7 FRAG lookup precedes ExclX target resolution"
    "No frag called r7_missing_left" [ExclX "rule:r7_missing_target",left]
  val _ = List.app context_case ["register","restore","change","remove"]
end;

(* R7 extension-only controls: projection through wrapper metadata, no descent
   into AC/Cong, and initial goal-time Context still selects the strategy. *)
local
  val missing = markerSyntax.L "r7_branch_missing_label"
  val goal = ([],mk_var ("r7_branch_goal",bool))
  val split = markerLib.Split TRUTH
  fun bound name th = ADD_ASSUM
    (mk_comb (boolSyntax.bounded_tm,mk_var (name,bool))) th
  fun counted f = let
    val meter = Count.mk_meter ()
    val result = Exn.capture f ()
  in (result,#prims (Count.read meter)) end
  fun stage_count (name,th) = let
    val (_,expected) = counted (fn () => markerLib.dest_directive th)
    val (result,actual) = counted
      (fn () => runtac (SIMP_TAC empty_ss [th,missing]) goal)
    val correct = case result of
        Exn.Exn (HOL_ERR e) => String.isSubstring
          "No assumption with label r7_branch_missing_label"
          (Feedback.message_of e)
      | _ => false
  in
    tprint ("R7 pure Split projection: " ^ name);
    if correct andalso expected > 0 andalso actual = expected then OK ()
    else die ("one decoder=" ^ Int.toString expected ^
              ", tactic=" ^ Int.toString actual)
  end
  val _ = List.app stage_count
    [("bare",split),
     ("Req0",markerLib.mk_Req0 split),
     ("ReqD",markerLib.mk_ReqD split),
     ("valid bound",bound "2" split),
     ("malformed bound",bound "a_bad" split),
     ("malformed first, valid later",bound "~3" (bound "a_bad" split)),
     ("mixed wrappers",markerLib.mk_Req0
        (markerLib.mk_ReqD (bound "2" split))),
     ("Cong does not expose Split",markerLib.Cong split),
     ("AC does not expose Split",markerLib.AC split TRUTH)]

  (* ExclX inspection is proof-free, including wrapper payloads. A missing
     label must win before bounds/requirements or target lookup. *)
  val exclusion = ExclX "case:r7_missing_type"
  fun exclusion_stage (name,th) = let
    val (_,expected) = counted (fn () => markerLib.dest_directive th)
    val (constructed,construction_count) = counted
      (fn () => SIMP_TAC empty_ss [th,missing])
    val (result,actual) = counted
      (fn () => runtac (Exn.release constructed) goal)
    val correct = case result of
        Exn.Exn (HOL_ERR e) => String.isSubstring
          "No assumption with label r7_branch_missing_label"
          (Feedback.message_of e)
      | _ => false
  in
    tprint ("R7 pure ExclX inspection: " ^ name);
    if correct andalso construction_count = 0 andalso actual = expected
    then OK () else die "ExclX caused early decoding/target resolution"
  end
  val _ = List.app exclusion_stage
    [("bare",exclusion), ("Req0",Req0 exclusion),
     ("ReqD",ReqD exclusion), ("Once",Once exclusion),
     ("malformed bound",bound "a_bad" exclusion),
     ("Req0 Once",Req0 (Once exclusion))]

  val cfg = {strip=false,elimvars=false,droptrues=false,oldestfirst=true}
  val builders =
    [("ASM_SIMP_TAC",ASM_SIMP_TAC empty_ss),
     ("SIMP_TAC",SIMP_TAC empty_ss),
     ("global_simp_tac",global_simp_tac cfg empty_ss)]
  val p = mk_var ("r7_saved_sf_p",bool)
  val solved = SPEC p boolTheory.EXCLUDED_MIDDLE
  val gl = ([],concl solved)
  fun saved_sf (label,build) (initial,target) = let
    val saved = Context.snapshot ()
    val name = "r7_saved_sf_" ^ label
    val directive = markerLib.FRAG name
    fun run () = let
      val _ = register_frag (name_ss name (rewrites []))
      val plain = Context.snapshot ()
      val _ = Context.restore saved
      val _ = register_frag (name_ss name
        (solver_ss (mk_tactic_solver ("r7 saved solver",ACCEPT_TAC solved))))
      val strategy = Context.snapshot ()
      fun select "absent" = Context.restore saved
        | select "plain" = Context.restore plain
        | select _ = Context.restore strategy
      val _ = select initial
      val constructed = Exn.capture build [directive]
      val _ = select target
      val result = Exn.capture
        (fn () => runtac (VALID (Exn.release constructed)) gl) ()
      val expected = if target = "plain" then [gl] else []
    in
      tprint ("R7 goal-time SF " ^ label ^ ": " ^ initial ^ " -> " ^ target);
      case result of
          Exn.Res (sgs,_) =>
            if list_eq goal_eq expected sgs then OK ()
            else die "saved tactic selected its construction-time strategy"
        | _ => die "saved SF tactic failed"
    end
  in Portable.finally (fn () => Context.restore saved) run () end
  val _ = List.app
    (fn builder => List.app (saved_sf builder)
      [("absent","strategy"),("strategy","plain"),("plain","strategy")])
    builders
  val _ = let
    val ss = add_unsafe_solver
      (mk_tactic_solver ("r7 explicit solver",ACCEPT_TAC solved)) empty_ss
    val result = Exn.capture
      (fn () => runtac (VALID (GEN_SIMP_TAC {safe=false} ss [])) gl) ()
  in
    tprint "R7 explicit GEN_SIMP_TAC still bypasses old dispatch";
    case result of Exn.Res ([],_) => OK ()
      | _ => die "explicit generalized strategy stopped solving"
  end
in
  ()
end

(* P1: unread generic facts must still protect binders; readable facts
   retain reducer-prepend / solver-append / recursive-prepend ordering. *)
val _ = let
  val x = ``perf_capture_x:bool``
  val capture_rule = ASSUME ``perf_capture_c = (perf_capture_x:bool)``
  val input = ``\perf_capture_x:bool. perf_capture_c:bool``
  val output = ``\perf_capture_y:bool. perf_capture_x:bool``
  val bare_data = traversedata_for_ss pureSimps.pure_ss
  val installed_data = traversedata_for_ss
    (pureSimps.pure_ss ++ rewrites [capture_rule])
  fun capture data context = Traverse.TRAVERSE_WITH_CONTEXT
    Traverse.ParentFirst (data,Traverse.default_config) context
  val _ = convtest
    ("P1 no provider: reducer facts retain hypothesis free variables",
     capture bare_data {reducer_context=[capture_rule],solver_context=[]},
     input,output)
  val _ = convtest
    ("P1 no provider: solver facts retain hypothesis free variables",
     capture installed_data
       {reducer_context=[],solver_context=[ASSUME x]},input,output)

  val a = ``perf_order_a:bool``
  val b = ``perf_order_b:bool``
  val condition = ``perf_order_condition:bool``
  val reducers = map ASSUME [``perf_r1:bool``,``perf_r2:bool``]
  val solvers = map ASSUME [``perf_s1:bool``,``perf_s2:bool``]
  val nested = map ASSUME [``perf_n1:bool``,``perf_n2:bool``]
  fun order_test subgoal = let
    val seen = ref ([] : term list list)
    fun record thms = seen := !seen @ [map concl thms]
    fun subgoaler {context_thms,...} tm =
      (record context_thms; EQT_INTRO (ASSUME tm))
    fun solver {context_thms,...} tm =
      (record context_thms; ASSUME tm)
    val reducer = lifted_reducer
      {name=NONE,initial=EMPTY_CONTEXT,
       addcontext=fn (ctxt,_) => ctxt,
       apply=fn {solver,stack,...} => fn tm =>
         if aconv tm a orelse aconv tm b then
           (ignore (solver stack condition); NO_CONV tm)
         else NO_CONV tm}
    val congproc : Opening.congproc = fn _ => fn {depther,...} => fn tm =>
      if aconv tm a then
        (ignore (QCONV (TRY_CONV
           (depther (nested,boolSyntax.equality))) b);
         raise UNCHANGED)
      else NO_CONV tm
    val data : Traverse.traverse_data =
      {rewriters=[reducer],dprocs=[],limit=NONE,
       relation=boolSyntax.equality,
       travrules=Travrules.TRAVRULES
         {relations=[Travrules.EQ_preorder],congprocs=[congproc],
          weakenprocs=[]}}
    val config : Traverse.traverse_config =
      {subgoaler=if subgoal then SOME subgoaler else NONE,
       solvers=if subgoal then [] else [{name="order",solve=solver}],
       cond_depth=NONE,term_ord=NONE}
    val _ = QCONV (TRY_CONV
      (Traverse.TRAVERSE_WITH_CONTEXT Traverse.ParentFirst
        (data,config) {reducer_context=reducers,solver_context=solvers})) a
    val expected = map (map concl)
      [reducers @ solvers,nested @ reducers @ solvers]
  in
    tprint ("P1 " ^ (if subgoal then "subgoaler" else "unsafe solver") ^
            ": exact initial and recursive fact order");
    if ListPair.allEq
         (fn (xs,ys) => ListPair.allEq
           (fn (x,y) => aconv x y) (xs,ys)) (!seen,expected)
    then OK () else die "generic fact sequence changed"
  end
  val _ = order_test true
  val _ = order_test false
in
  ()
end

(* Legacy factory scheduling and live reducer controls must interact in
   baseline order, while the private construction-time context is reused. *)
val _ = let
  val a = ``c2_a:bool``
  val b = ``c2_b:bool``
  val ab = ASSUME (boolSyntax.mk_eq (a,b))
  val probe = (a,b)
  val log = ref ([] : string list)
  fun record s = log := !log @ [s]
  fun reject tm = NO_CONV tm
  exception C2Context
  val additions = ref 0
  fun addcontext (ctxt,_) =
    (additions := !additions + 1; ctxt)
  val mutator = Traverse.CONTEXT_REDUCER
    {name=NONE,initial=C2Context,addcontext=addcontext,
     apply=fn {cond_depth,term_ord,...} => fn tm =>
       if aconv tm a then
         (if cond_depth = 13 andalso
             term_ord probe = Cond_rewr.ac_term_ord probe
          then record "context-live-13" else raise Fail "context controls";
          Cond_rewr.stack_limit := 23;
          reject tm)
       else reject tm}
  val native = Traverse.CONFIG_REDUCER
    {name=NONE,initial=C2Context,addcontext=fn (c,_) => c,
     apply=fn {cond_depth,term_ord,...} => fn tm =>
       if aconv tm a then
         (if not (Option.isSome cond_depth) andalso
             !Cond_rewr.stack_limit = 23 andalso
             term_ord probe = Cond_rewr.ac_term_ord probe
          then record "config-none-live-23" else raise Fail "config controls";
          ab)
       else reject tm}
  val weakener : Opening.congproc = fn _ =>
    (record "weak-relation";
     fn _ => (record "weak-factory";
              Cond_rewr.stack_limit := 13;
              reject))
  val data : Traverse.traverse_data =
    {limit=NONE,rewriters=[mutator,native],dprocs=[],
     relation=boolSyntax.equality,
     travrules=Travrules.TRAVRULES
       {relations=[Travrules.EQ_preorder],congprocs=[],
        weakenprocs=[weakener]}}
  val cv = Traverse.TRAVERSE data [ASSUME ``c2_fact:bool``]
  val _ = tprint "C2 legacy private context initialized before application"
  val _ = if !additions = 1 andalso null (!log) then OK ()
          else die "legacy context or factory construction stage changed"
  val old = !Cond_rewr.stack_limit
  val _ = Portable.finally (fn () => Cond_rewr.stack_limit := old)
    (fn () =>
      (convtest ("C2 weakener factory feeds live reducer controls",cv,a,b);
       convtest ("C2 CONFIG NONE/order and live context survive reuse",cv,a,b)))
    ()
  val _ = tprint "C2 factory order and reusable context callback count"
  val expected = ["weak-relation","weak-factory","context-live-13",
                  "config-none-live-23"]
  val _ = if !additions = 1 andalso !log = expected @ expected then OK ()
          else die "factory/reducer callback order or context reuse changed"
in () end

(* REWR_CONV constructs PART_MATCH eagerly.  The old congruence wrapper
   calls relation reflexivity BEFORE that factory, even for a quantified
   equation returned by an ordinary reducer.  Keep this after the existing
   Count pins: mk_meter leaves counting enabled. *)
local
  open OrdinarySimp
  structure pureSimps = OrdinaryPure
  structure congLib = OrdinaryCong
  structure Traverse = OrdinaryTraverse
  exception StageContext
  exception StageEvent of unit ref
  val payload = ref ()
  val armed = ref false
  val observed = ref (NONE : int option)
  val meter = ref (NONE : Count.meter option)
  val input = mk_var ("cong_stage_input",bool)
  val x = mk_var ("cong_stage_x",bool)
  val equation = GEN x (REFL x)
  val fixture_ok = null (hyp equation) andalso
    aconv (concl equation)
      (boolSyntax.mk_forall (x,boolSyntax.mk_eq (x,x)))
  fun reflexivity {Rinst,arg} =
    if !armed then
      (observed := SOME (#prims (Count.read (valOf (!meter))));
       raise StageEvent payload)
    else DISCH arg (ASSUME arg)
  val preorder = Travrules.PREORDER
    (boolSyntax.implication,Drule.IMP_TRANS,reflexivity)
  val cs = congLib.mk_congset
    [congLib.CSFRAG {relations=[preorder],rewrs=[],congs=[],dprocs=[]}]
  val reducer = Traverse.REDUCER
    {name=SOME "congLib factory stage",initial=StageContext,
     addcontext=fn (ctxt,_) => ctxt,
     apply=fn {relation=(rel,_),...} => fn tm =>
       if Opening.samerel rel boolSyntax.implication then
         (armed := true; meter := SOME (Count.mk_meter ()); equation)
       else NO_CONV tm}
  val cv = congLib.CONGRUENCE_SIMP_QCONV boolSyntax.implication cs
    (pureSimps.pure_ss ++ dproc_ss reducer) []
  val caught = (ignore (cv input); NONE) handle e => SOME e
  val exact_event = case caught of
      SOME (StageEvent r) => Portable.pointer_eq (r,payload)
    | _ => false
in
  val _ = tprint "congLib reflexivity precedes rewrite factory primitives"
  val _ = if fixture_ok andalso !observed = SOME 0 then OK ()
          else die "rewrite factory ran before the reflexivity callback"
  val _ = tprint "congLib reflexivity preserves foreign tag and payload"
  val _ = if exact_event then OK ()
          else die "reflexivity exception constructor or payload changed"
end

(* Paired native runners and tracked default/configured projections share
   compiled rules and controls. Ordinary optional eligibility stays below. *)
local
  fun check name condition =
    (tprint name;
     if condition then OK () else die "native runner regression")
  fun same_terms xs ys =
    length xs = length ys andalso
    List.all (fn x => List.exists (aconv x) ys) xs
  fun same_thm left right =
    aconv (concl left) (concl right) andalso
    same_terms (hyp left) (hyp right) andalso
    same_terms (thm_frees left) (thm_frees right)
  fun total cv = QCONV (TRY_CONV cv)

  val p = ``paired_condition:bool``
  val guard = ``paired_guard (paired_parameter:'a):bool``
  val target = ``paired_predicate (paired_argument:'b):bool``
  (* Do not GEN_ALL: guard's free parameter must remain in the hypotheses. *)
  val rule = DISCH p (ADD_ASSUM guard (EQT_INTRO (ASSUME p)))
  val expected = ADD_ASSUM guard (EQT_INTRO (ASSUME target))
  val runners = Cond_rewrExt.COND_REWR_CONVS ("paired condition",rule) false
  fun configured depth solver stack = #configured runners
    {solver=solver,stack=stack,cond_depth=depth,
     term_ord=Cond_rewr.ac_term_ord}
  val solver_calls = ref ([] : term list list)
  fun solve stack tm =
    (solver_calls := stack :: !solver_calls; ASSUME tm)
  val legacy_th = #legacy runners solve [] target
  val configured_th = configured NONE solve [] target
  val public_th =
    Cond_rewr.COND_REWR_CONV ("public condition",rule) false solve [] target
  val _ = check "paired runners preserve theorem, hypotheses and free params"
    (same_thm legacy_th expected andalso
     same_thm configured_th expected andalso same_thm public_th expected
     andalso ListPair.allEq
       (fn (xs,ys) => same_terms xs ys)
       (!solver_calls,[[target],[target],[target]]))

  (* Construct the runner before a preceding failed candidate mutates the
     default. NONE must read it at the conditional candidate, not earlier. *)
  fun depth_case runner initial changed succeeds =
    Lib.with_flag (Cond_rewr.stack_limit,initial)
      (fn () => let
         val calls = ref 0
         fun solve _ tm = (calls := !calls + 1; ASSUME tm)
         val cv = runner solve []
         fun first tm = (Cond_rewr.stack_limit := changed; NO_CONV tm)
         val th = total (first ORELSEC cv) target
       in
         same_thm th (if succeeds then expected else REFL target)
         andalso !calls = (if succeeds then 1 else 0)
       end) ()
  val saved_depth = !Cond_rewr.stack_limit
  val depth_checks =
    [depth_case (#legacy runners) 0 1 true,
     depth_case (#legacy runners) 1 0 false,
     depth_case (configured NONE) 0 1 true,
     depth_case (configured NONE) 1 0 false,
     depth_case (configured (SOME 0)) 0 4 false,
     depth_case (configured (SOME 1)) 4 0 true,
     depth_case
       (Cond_rewr.COND_REWR_CONV ("public live depth",rule) false)
       0 1 true]
  val _ = check "paired NONE depth is live; SOME zero/one remain isolated"
    (List.all I depth_checks andalso
     !Cond_rewr.stack_limit = saved_depth)

  (* The wrappers deliberately turn non-HOL_ERR solver failures into
     HOL_ERR, except Interrupt. Compare that observable result, not an
     unsupported assertion about retained foreign exception payloads. *)
  exception PairedStop
  val solver_errors =
    [mk_HOL_ERR "paired solver" "application" "deliberate failure",
     Conv.UNCHANGED,PairedStop,Portable.Interrupt]
  fun failure runner error =
    (runner (fn _ => fn _ => raise error) [] target;
     NONE)
    handle Portable.Interrupt => SOME ("Interrupt","Interrupt")
         | e => SOME (General.exnName e,Feedback.exn_to_string e)
  fun same_failure error =
    let
      val legacy = failure (#legacy runners) error
      val observed_configured = failure (configured NONE) error
      val explicit = failure (configured (SOME 1)) error
    in
      Option.isSome legacy andalso legacy = observed_configured andalso
      legacy = explicit
    end
  val failure_checks = Lib.with_flag (Cond_rewr.stack_limit,1)
    (fn () => map same_failure solver_errors) ()
  val _ = check "paired solver failures preserve wrapping and Interrupt"
    (List.all I failure_checks andalso
     !Cond_rewr.stack_limit = saved_depth)

  (* Type-specific cutover: the tracked default rewriter is now explicitly
     LIFTED REDUCER (not REDUCER); configured extraction stays CONFIG.
     Both getters are total. Quota/proof/maker checks below are unchanged.
     Optional eligibility and the literal ordinary REDUCER client remain
     separately tested against OrdinarySimp, with ordinary pointer checks. *)
  fun ordinary reducer =
    Traverse.reducer_kind reducer = Traverse.LiftedReducer
  fun configured_rewriter data =
    case #rewriters (data : Traverse.traverse_data) of
        [r] => Traverse.reducer_kind r = Traverse.ConfigReducer
      | _ => false
  fun native_shape data =
    not (null (#rewriters (data : Traverse.traverse_data))) andalso
    List.all ordinary (#rewriters data @ #dprocs data)

  (* The quota is attached to an installed native occurrence. Alternating
     real projections must spend that same quota in either starting order. *)
  fun quota_case legacy_first = let
    val a = ``projection_quota_a:bool``
    val b = ``projection_quota_b:bool``
    val equation = ASSUME (mk_eq (a,b))
    val compiles = ref 0
    val base = empty_ss ++ SSFRAG
      {name=NONE,convs=[],rewrs=[],ac=[],dprocs=[],congs=[],
       filter=SOME (fn th => (compiles := !compiles + 1; [th]))}
    val ss = base ++ rewrites [Ntimes equation 2]
    val before_projection = !compiles
    val public = traversedata_for_ss ss
    val configured = #1 (xtraversedata_for_ss ss)
    val legacy_cv = total (Traverse.TRAVERSE public [])
    val configured_cv = total (Traverse.TRAVERSE configured [])
    val construction_ok = before_projection = 1 andalso
      !compiles = before_projection andalso native_shape public andalso
      configured_rewriter configured
    val (first,second) = if legacy_first
      then (legacy_cv,configured_cv) else (configured_cv,legacy_cv)
    val th1 = first a
    val th2 = second a
    val th3 = first a
    val th4 = second a
  in
    construction_ok andalso same_thm th1 equation andalso
    same_thm th2 equation andalso same_thm th3 (REFL a) andalso
    same_thm th4 (REFL a) andalso !compiles = before_projection
  end
  val quota_checks = [quota_case true,quota_case false]
  val _ = check "public/configured projections share quotas without compiling"
    (List.all I quota_checks)

  (* Extract again only after spending a use, then after exhaustion. The
     complete explicit engine refreshes contexts, not installed quotas. *)
  fun late_quota_case legacy_first = let
    val a = ``late_quota_a:bool``
    val b = ``late_quota_b:bool``
    val equation = ASSUME (mk_eq (a,b))
    val compiles = ref 0
    val compilation_events = ref 0
    fun watch (2,Trace.LZ_TEXT text) =
          if String.isPrefix "New rewrite: " (text ()) then
            compilation_events := !compilation_events + 1
          else ()
      | watch _ = ()
    val base = empty_ss ++ SSFRAG
      {name=NONE,convs=[],rewrs=[],ac=[],dprocs=[],congs=[],
       filter=SOME (fn th => (compiles := !compiles + 1; [th]))}
    val ss = base ++ rewrites [Ntimes equation 2]
    fun build legacy = total
      (if legacy then Traverse.TRAVERSE (traversedata_for_ss ss) []
       else Traverse.XTRAVERSE (xtraversedata_for_ss ss) [])
    val listener = "late projection quota compilation"
    val _ = Listener.add_listener Trace.trace_hook (listener,watch)
    fun run () = let
      val first = build legacy_first
      val th1 = first a
      val second = build (not legacy_first)
      val th2 = second a
      val exhausted = [first a,second a,build true a,build false a]
    in
      same_thm th1 equation andalso same_thm th2 equation andalso
      List.all (fn th => same_thm th (REFL a)) exhausted andalso
      !compiles = 1 andalso !compilation_events = 0
    end
  in
    Portable.finally
      (fn () => ignore (Listener.remove_listener Trace.trace_hook listener))
      run ()
  end
  val _ = check "late public/extended extraction cannot refresh spent quotas"
    (late_quota_case true andalso late_quota_case false)

  (* Views and preserving-control replay must carry both runners and the
     same remaining quota, not merely equivalent initial declarations. *)
  val view_a = ``projection_view_a:bool``
  val view_b = ``projection_view_b:bool``
  val view_eq = ASSUME (mk_eq (view_a,view_b))
  val removable = SSFRAG
    {name=SOME "paired removable",convs=[],rewrs=[],ac=[],
     filter=NONE,dprocs=[],congs=[]}
  val view_base = pureSimps.pure_ss ++ removable ++
                  rewrites [Ntimes view_eq 3]
  val view_source = hd (rewrite_source_handles view_base)
  val viewed = view_base ++ rewrite_views [(view_source,view_eq)]
  val view_native = total (Traverse.TRAVERSE
    (traversedata_for_ss view_base) [])
  val view_configured = total (Traverse.TRAVERSE
    (#1 (xtraversedata_for_ss viewed)) [])
  val view_first = view_native view_a
  val replayed = remove_ssfrags_preserving_controls
    ["paired removable"] viewed
  val replay_native = total (Traverse.TRAVERSE
    (traversedata_for_ss replayed) [])
  val view_second = view_configured view_a
  val view_third = replay_native view_a
  val view_exhausted = [view_native view_a,view_configured view_a,
                        replay_native view_a]
  val _ = check "views and preserving replay share both runner controls"
    (same_thm view_first view_eq andalso same_thm view_second view_eq
     andalso same_thm view_third view_eq andalso
     List.all (fn th => same_thm th (REFL view_a)) view_exhausted)

  exception ProjectionContext
  val additions = ref 0
  fun addcontext (context,_) = (additions := !additions + 1; context)
  val ordinary_probe = lifted_reducer
    {name=NONE,initial=ProjectionContext,addcontext=addcontext,
     apply=fn _ => NO_CONV}
  val context_probe = Traverse.CONTEXT_REDUCER
    {name=NONE,initial=ProjectionContext,addcontext=addcontext,
     apply=fn _ => NO_CONV}
  val config_probe = Traverse.CONFIG_REDUCER
    {name=NONE,initial=ProjectionContext,addcontext=addcontext,
     apply=fn _ => NO_CONV}
  val base = bool_ss ++ dproc_ss ordinary_probe
  val rejecting_solver : Traverse.ssolver =
    {name="projection solver",solve=fn _ => NO_CONV}
  val excluded =
    [set_subgoaler (fn _ => REFL) base,
     set_unsafe_solvers [rejecting_solver] base,
     set_cond_depth 4 base,
     set_term_ord Cond_rewr.ac_term_ord base,
     base ++ dproc_ss context_probe,
     base ++ dproc_ss config_probe]
  val accepted_inputs =
    [base,set_safe_solvers [rejecting_solver] base,
     set_looper ("projection unused looper",K ALL_TAC) base]
  (* Adding a fragment legitimately calls existing collectors, even for
     []. Bracket extraction, rather than counting fixture construction. *)
  val before_rejected = !additions
  val rejected = map traversedata_for_ss excluded
  val after_rejected = !additions
  val accepted = map traversedata_for_ss accepted_inputs
  val after_accepted = !additions
  val constructor_inputs = empty_ss :: bool_ss :: base :: excluded

  val ordinary_eligibility = let
    open OrdinarySimp OrdinaryBool
    (* Ordinary sets have no optional/configured getters.
       Their total baseline projection is inert for every ordinary input;
       all strategy/configured cases remain in the tracked tests above. *)
    val additions = ref 0
    val probe = OrdinaryTraverse.REDUCER
      {name=NONE,initial=ProjectionContext,
       addcontext=fn (c,_) => (additions := !additions + 1; c),
       apply=fn _ => NO_CONV}
    val base = bool_ss ++ dproc_ss probe
    val inputs = [empty_ss,bool_ss,base,limit 4 base,
                  unlimit (limit 4 base),base ++ empty_ssfrag]
    val before_extraction = !additions
    val OrdinaryTraverse.REDUCER _ =
      hd (#rewriters (traversedata_for_ss empty_ss))
    fun ordinary (OrdinaryTraverse.REDUCER _) = true
    fun public_projection ss = let
      val public = traversedata_for_ss ss
      val repeated = traversedata_for_ss ss
      val native = case #rewriters public of
          [OrdinaryTraverse.REDUCER _] => true | _ => false
    in
      native andalso
      List.all ordinary (#rewriters public @ #dprocs public) andalso
      Portable.pointer_eq (#dprocs public,#dprocs repeated) andalso
      Portable.pointer_eq (#travrules public,#travrules repeated) andalso
      aconv (#relation public) boolSyntax.equality andalso
      #limit public = #limit repeated
    end
    val results = map public_projection inputs
    val data = traversedata_for_ss base
  in
    List.all I results andalso not (null (#dprocs data)) andalso
    #limit (traversedata_for_ss (limit 4 base)) = SOME 4 andalso
    before_extraction = !additions
  end
  (* Context/config procedures cannot inhabit the restored ordinary type.
     Their former optional-rejection cases above are instead tracked total
     projections: preserve their exact extension dproc list and CONFIG
     companion, with zero extraction callbacks, not unlike-type equality. *)
  fun public_projection ss = let
    val public = traversedata_for_ss ss
    val extended = #1 (xtraversedata_for_ss ss)
    val native = case #rewriters public of
        [r] => Traverse.reducer_kind r = Traverse.LiftedReducer
      | _ => false
  in
    native andalso
    Portable.pointer_eq (#dprocs public,#dprocs extended) andalso
    Portable.pointer_eq (#travrules public,#travrules extended) andalso
    aconv (#relation public) boolSyntax.equality andalso
    #limit public = #limit extended
  end
  val public_checks = map public_projection constructor_inputs
  val configured_shapes = map (configured_rewriter o #1 o
                                xtraversedata_for_ss) constructor_inputs
  val _ = check "public projection preserves REDUCER and supplied dprocs"
    (List.all I public_checks andalso List.all I configured_shapes andalso
     !additions = after_accepted)
  val _ = check "native projection eligibility is pure and conservative"
    (before_rejected = after_rejected andalso
     after_rejected = after_accepted andalso
     after_accepted = !additions andalso ordinary_eligibility andalso
     List.all (fn data => not (null (#dprocs data))) rejected andalso
     List.all (fn data => native_shape data andalso
                         not (null (#dprocs data))) accepted)

  (* Tracked default extraction ignores simpset-specific configuration;
     these settings no longer inhabit the ordinary simpset type. *)
  val default_a = ``projection_default_a:bool``
  val default_b = ``projection_default_b:bool``
  val default_condition = ``projection_default_condition:bool``
  val default_rule = ASSUME
    (mk_imp (default_condition,mk_eq (default_a,default_b)))
  val default_base = limit 3 (pureSimps.pure_ss ++ rewrites [default_rule])
  val config_calls = ref 0
  fun unused_subgoaler _ tm = (config_calls := !config_calls + 1; REFL tm)
  val unused_solver : Traverse.ssolver =
    {name="projection unused solver",solve=fn _ => fn tm =>
      (config_calls := !config_calls + 1; NO_CONV tm)}
  fun unused_order pair =
    (config_calls := !config_calls + 1; Cond_rewr.ac_term_ord pair)
  val default_inputs =
    [set_subgoaler unused_subgoaler default_base,
     set_unsafe_solvers [unused_solver] default_base,
     set_cond_depth 0 default_base,
     set_term_ord unused_order default_base]
  fun default_case ss = let
    val data = traversedata_for_ss ss
    val th = total (Traverse.TRAVERSE data [ASSUME default_condition])
      default_a
  in
    #limit data = SOME 3 andalso same_thm th (UNDISCH default_rule)
  end
  val default_checks = Lib.with_flag (Cond_rewr.stack_limit,4)
    (fn () => map default_case default_inputs) ()
  val configured_zero = total (Traverse.XTRAVERSE
    (xtraversedata_for_ss (set_cond_depth 0 default_base))
    [ASSUME default_condition]) default_a
  val _ = check "public projection omits configuration; extended keeps it"
    (List.all I default_checks andalso !config_calls = 0 andalso
     same_thm configured_zero (REFL default_a) andalso
     !Cond_rewr.stack_limit = saved_depth)

  (* Positive controls make solver/order omission observable: a solved
     condition above bypasses unsafe solvers, and ordinary rules need no
     orientation check. These callbacks must affect only extended data. *)
  val solver_calls = ref 0
  val proving_solver : Traverse.ssolver =
    {name="projection proving solver",solve=fn _ => fn tm =>
      if aconv tm default_condition then
        (solver_calls := !solver_calls + 1; ASSUME tm)
      else NO_CONV tm}
  val solver_ss = set_unsafe_solvers [proving_solver] default_base
  val public_unsolved = total (Traverse.TRAVERSE
    (traversedata_for_ss solver_ss) []) default_a
  val before_solver = !solver_calls
  val extended_solved = total (Traverse.XTRAVERSE
    (xtraversedata_for_ss solver_ss) []) default_a
  val _ = check "public omits unsafe solver; extended invokes it"
    (same_thm public_unsolved (REFL default_a) andalso before_solver = 0
     andalso same_thm extended_solved (UNDISCH default_rule) andalso
     !solver_calls = 1)

  val order_calls = ref 0
  fun reverse_order pair =
    (order_calls := !order_calls + 1;
     case Cond_rewr.ac_term_ord pair of
         LESS => GREATER | EQUAL => EQUAL | GREATER => LESS)
  val order_ss = set_term_ord reverse_order
    (pureSimps.pure_ss ++ rewrites [boolTheory.EQ_SYM_EQ])
  val ascending = ``projection_order_a:'a = projection_order_b``
  val descending = ``projection_order_b:'a = projection_order_a``
  val public_ordered = total (Traverse.TRAVERSE
    (traversedata_for_ss order_ss) []) descending
  val before_order = !order_calls
  val extended_ordered = total (Traverse.XTRAVERSE
    (xtraversedata_for_ss order_ss) []) ascending
  val _ = check "public uses default order; extended invokes custom order"
    (aconv (concl public_ordered) (mk_eq (descending,ascending)) andalso
     null (hyp public_ordered) andalso before_order = 0 andalso
     aconv (concl extended_ordered) (mk_eq (ascending,descending)) andalso
     null (hyp extended_ordered) andalso !order_calls > 0)

  (* Type-specific change: tracked projection is total even for contextual
     procedures. Replace optional NONE with LIFTED-native/exact-dproc shape
     checks; retain configured invocation controls, proofs and collectors. *)
  val fallback_a = ``projection_fallback_a:bool``
  val fallback_b = ``projection_fallback_b:bool``
  val fallback_eq = ASSUME (mk_eq (fallback_a,fallback_b))
  val seen = ref ([] : int option list)
  fun rewrite depth tm =
    if aconv tm fallback_a then
      (seen := depth :: !seen;
       if depth = SOME 1 then fallback_eq else NO_CONV tm)
    else NO_CONV tm
  val fallback_reducers =
    [Traverse.CONTEXT_REDUCER
       {name=NONE,initial=ProjectionContext,addcontext=addcontext,
        apply=fn {cond_depth,...} => rewrite (SOME cond_depth)},
     Traverse.CONFIG_REDUCER
       {name=NONE,initial=ProjectionContext,addcontext=addcontext,
        apply=fn {cond_depth,...} => rewrite cond_depth}]
  fun fallback_case reducer = let
    val ss = set_cond_depth 1 (pureSimps.pure_ss ++ dproc_ss reducer)
    val prior_additions = !additions
    val native = traversedata_for_ss ss
    val configured = xtraversedata_for_ss ss
    val cv = SIMP_CONV ss [TRUTH]
    val constructed = !additions
    val first = cv fallback_a
    val after_first = !additions
    val second = cv fallback_a
    val stages = [constructed-prior_additions,after_first-prior_additions,
                  !additions-prior_additions]
    val _ = tprint "configured fallback collector construction/use counts"
    val _ = if stages = [0,1,2] then OK ()
            else die "fallback refreshed contexts at the wrong stage"
  in
    (case #rewriters native of
         [r] => Traverse.reducer_kind r = Traverse.LiftedReducer
       | _ => false) andalso
    Portable.pointer_eq (#dprocs native,#dprocs (#1 configured)) andalso
    configured_rewriter (#1 configured) andalso
    #cond_depth (#2 configured) = SOME 1 andalso
    same_thm first fallback_eq andalso same_thm second fallback_eq
  end
  val fallback_checks = Lib.with_flag (Cond_rewr.stack_limit,0)
    (fn () => map fallback_case fallback_reducers) ()
  val _ = check "rejected contextual procedures retain configured fallback"
    (List.all I fallback_checks andalso
     !seen = [SOME 1,SOME 1,SOME 1,SOME 1] andalso
     !Cond_rewr.stack_limit = saved_depth)
in
  ()
end

val _ = exit_count0 failcount

end (* struct *)
