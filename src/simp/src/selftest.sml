open HolKernel Parse boolLib simpLib
open testutils boolSimps BackchainingLib

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
      (VALID (ASM_SIMP_TAC bool_ss [markerSyntax.Abbr`y`]))
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
                  SIMP_TAC bool_ss [Once EQ_SYM_EQ] THEN
                  POP_ASSUM ACCEPT_TAC) g)
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
  open boolSimps
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
  open boolSimps
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
  val doit = ASM_SIMP_TAC bool_ss []
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
  infloop_protect "CONJ_ss with T=F and F=T assumptions (if hangs, it's failed)" check doit t
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
        require_msg testresult printgoals (VALID (ASM_SIMP_TAC pure_ss thl))
                    (asms,i)
      end
  val oneone = Q.prove(‘ONE_ONE f ==> !x y. (f x = f y) <=> (x = y)’,
                       REWRITE_TAC[ONE_ONE_THM] >> rpt strip_tac >> eq_tac >>
                       strip_tac >- (first_x_assum irule >> ASM_REWRITE_TAC[])>>
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
       require_msg (testresult outgs) printgoals tac ing)
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
    ("gs oldestfirst", gs gsc' bool_ss [], ([“x:'a = y”, “x:'a = z”], “p:bool”),
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

val _ = exit_count0 failcount
