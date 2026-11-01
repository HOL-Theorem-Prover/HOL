open HolKernel Parse boolLib bossLib DB
open testutils

val _ = new_theory "scratch"

val _ = print "\n"

val goal_compare = pair_compare(list_compare Term.compare, Term.compare)
val goals_compare = list_compare goal_compare
fun goals_eq gs1 gs2 = goals_compare (gs1, gs2) = EQUAL

fun listp p xs = "[" ^ String.concatWith ", " (map p xs) ^ "]"
fun pairp (p1, p2) (x,y) = "(" ^ p1 x ^ ", " ^ p2 y ^ ")"

val goal_toString =
    pairp (listp term_to_string, term_to_string)
val goals_toString = listp goal_toString

fun test_CONV (c,nm) (t, expected) = let
  val _ = tprint (nm^" on `"^term_to_string t^"`")
  val th = Conv.QCONV c t
in
  if aconv (rhs (concl th)) expected then OK()
  else die "FAILED!\n"
end handle HOL_ERR _ => die "FAILED (not even an eqn)!"

val _ = set_trace "Unicode" 0

val _ = app (test_CONV (EVAL,"EVAL")) [
      (``option_CASE (NONE : 'a option) (n:'b) f``, ``n:'b``),
      (``option_CASE (SOME (x:'a)) (n:'b) f``, ``f (x:'a):'b``),
      (``list_CASE ((h::t) : 'a list) (n:'b) f``,
       ``f (h:'a) (t:'a list):'b``),
      (``sum_CASE (INL 3) (\n. n) f``, ``3``),
      (``INL (x:'a) = INR (y:'b)``, ``F``),
      (``INL (x:'a) = INL x'``, ``x:'a = x'``)
];

val tydef_th = prove(
  ``?p. FST p /\ SND p``,
  EXISTS_TAC ``(T,T)`` THEN REWRITE_TAC []);

val _ = tprint "new_type_definition error message"
val _ =
    ignore (new_type_definition("mytydef", tydef_th))
    handle HOL_ERR herr =>
           if top_function_of herr <> "new_type_definition" orelse
              top_structure_of herr <> "Theory.Definition" orelse
              message_of herr <>
              "expected a theorem of the form \"?x. P x\""
           then
             die "FAILED"
           else OK()

val _ = tprint "Q.MATCH_ABBREV_TAC with underscores"
val goal = ([] : term list, ``(n + 10) * y <= 42315 /\ !x y:'a. x < f y``)
val (sgs, _) = runtac (Q.MATCH_ABBREV_TAC `a * _ <= b /\ _`) goal
val expectedg = ``(a:num) * y <= b /\ !x y:'a. x < f y``
val exab1 = ``Abbrev((a:num) = n + 10)``
val exab2 = ``Abbrev((b:num) = 42315)``
val _ = case sgs of
            [(asms, g')] =>
            if aconv g' expectedg andalso op_mem aconv exab1 asms andalso
               op_mem aconv exab2 asms andalso length asms = 2
            then
              OK()
            else die "FAILED!"
          | _ => die "FAILED!"

val _ = tprint "qhdtm_x_assum (1)"
val goal = ([``x = 3``, ``FACT n = 10``], ``n + x = 7``)
val (sgs, _) = runtac (qhdtm_x_assum `FACT` mp_tac) goal
val expectedg = ``(FACT n = 10) ==> (n + x = 7)``
val expecteda = ``x = 3``
val _ = case sgs of
            [([a], g)] => if aconv g expectedg andalso aconv a expecteda then
                            OK()
                          else die "FAILED!"
          | _ => die "FAILED!"

local

open match_goal

val n = ref 0;

fun test_assert P x =
  (tprint ("match_goal "^(Int.toString (!n))); n := !n + 1;
   if P x then OK() else die "FAILED!")

val (test1:matcher * mg_tactic) =
   (mg.a "H" `P_ /\ Q_`,
    fn (t,a) =>
      kill_asm(t"H")
      \\ strip_assume_tac(t"H" ))

val P = mk_var("P",bool)
val Q = mk_var("Q",bool)

val (g1:goal) = ([boolSyntax.mk_conj(P,Q)], boolSyntax.mk_neg(P))

val res1 =
    test_assert (goals_eq [([Q,P],boolSyntax.mk_neg(P))] o #1)
                (runtac (match1_tac test1) g1)

val test2 =
  [
    ([mg.abc `if b_ then _ else _`],
     fn (t,a) => (Cases_on`^(a"b")`))
    ,([],(K ALL_TAC):mg_tactic)
  ]

val res1' = test_assert (goals_eq [g1] o #1)
                        (runtac (first_match_tac test2) g1)

val g2 = ([``x:bool = if P then x' else x''``, ``x:bool``],``yi = if x then x'' else (ARB:bool)``)

val res2 = test_assert (equal 2 o length o #1)
  (runtac (first_match_tac test2) g2)

val (test3:matcher list * mg_tactic) =
  ([ mg.a "h1" `f_ _ = _`,
     mg.a "h2" `f_ _ = _`
   ],
   fn (a,t) =>
     disch_then (drule_thm (a"h1"))
     \\ disch_then (drule_thm (a"h2"))
     \\ disch_then ACCEPT_TAC)

val g3 = (
  [``f (x:num) = 3n``,
   ``g (y:num) = 5n``,
   ``f (y:num) = 4n``],
  ``(!(a:num) g (b:num) z1 z2. (f a = z1) ==> (g b = z2) ==> z1 + z2 < 7n) ==> 3 + 4 < 7n``)

val res3 = test_assert (List.null o #1)
  (runtac (match_tac test3) g3)

val (test4:matcher list * mg_tactic) =
  ([ mg.a "h1" `f_ _ = _`,
     mg.a "h2" `f_ _ = _`,
     mg.cb `(f_ _ = _) ==> _`
   ],
   fn (a,t) =>
     disch_then (drule_thm (a"h1"))
     \\ disch_then (drule_thm (a"h2")))

val g4 = (
  [``f (x:num) = 3n``,
   ``g (y:num) = 5n``,
   ``f (y:num) = 4n``],
  ``(!(a:num) g (b:num) z1 z2. (f a = z1) ==> (g b = z2) ==> z1 + z2 < 10n) ==> 3 + 4 < 10n``)

val res4 = test_assert (aconv ``3 + 4 < 10n ==> 3 + 4 < 10n`` o #2 o hd o #1)
  (runtac (match_tac test4) g4)

in end

local
val tyis = TypeBase.elts()
fun check tyi =
    let
      open TypeBasePure Portable
      val tynm = let val (thy,opn) = ty_name_of tyi in thy^"$"^opn end
      val _ = tprint ("Checking simpls for "^tynm)
      val simpls = map concl $ #rewrs $ simpls_of tyi
      val simpls_set = HOLset.addList(empty_tmset, simpls)
    in
      if HOLset.numItems simpls_set = length simpls then OK()
      else die "Duplicates exist"
    end
in
val _ = app check tyis
end (* local *)


local
val _ = Globals.interactive := true
val _ = Feedback.emit_MESG := false
val _ = Datatype`testrcd = <| fld1 : num ; fld2 : bool |>`;

fun test (msg, c) =
    let
      val _ = tprint ("Record constructor injectivity ("^msg^")")
    in
      require_msg (check_result (aconv ``(x:num = y) /\ (a <=> b)``))
                  term_to_string (rhs o concl o c)
                  ``testrcd x a = testrcd y b``;
      ()
    end
in
val _ = List.app test [("simp", SIMP_CONV (srw_ss()) []), ("EVAL", EVAL)]
end (* local *)

local
  open listSyntax
  fun mkl nm = mk_var(nm, mk_list_type alpha)
  val appl_t = list_mk_append (map mkl ["x", "y", "z"])
  val appr_t = mk_append(mkl "x", mk_append(mkl "y", mkl"z"))
in
val _ = tprint "Std simp left-normalises list"
val _ = require_msg (check_result (aconv appl_t o rhs o concl)) thm_to_string
                    (QCONV (SIMP_CONV (srw_ss()) [])) appr_t
val _ = tprint "Simp -* APPEND_ASSOC leaves list unchanged"
val _ = require_msg (check_result (aconv appr_t o rhs o concl)) thm_to_string
                    (QCONV (SIMP_CONV (srw_ss() -* ["APPEND_ASSOC"]) [])) appr_t
val _ = tprint "Simp -* list.APPEND_ASSOC leaves list unchanged"
val _ = require_msg (check_result (aconv appr_t o rhs o concl)) thm_to_string
                    (QCONV (SIMP_CONV (srw_ss() -* ["list.APPEND_ASSOC"]) []))
                    appr_t
val _ = tprint "Simp -* list.APPEND_ASSOC.1 leaves list unchanged"
val _ = require_msg (check_result (aconv appr_t o rhs o concl)) thm_to_string
                    (QCONV (SIMP_CONV (srw_ss() -* ["list.APPEND_ASSOC.1"]) []))
                    appr_t
val _ = tprint "Simp Excl APPEND_ASSOC leaves list unchanged"
val _ = require_msg (check_result (aconv appr_t o rhs o concl)) thm_to_string
                    (QCONV (SIMP_CONV (srw_ss()) [Excl "APPEND_ASSOC"])) appr_t
val _ = tprint "Simp Excl list.APPEND_ASSOC leaves list unchanged"
val _ = require_msg (check_result (aconv appr_t o rhs o concl)) thm_to_string
                    (QCONV (SIMP_CONV (srw_ss()) [Excl "list.APPEND_ASSOC"]))
                    appr_t
val _ = shouldfail {
      checkexn = (fn UNCHANGED => true | _ => false),
      printarg = fn _ => "simp Excl on arith d.p. leaves input unchanged",
      printresult = thm_to_string,
      testfn = SIMP_CONV (srw_ss() ++ ARITH_ss) [Excl "NUM_ARITH_DP"]
    } “4 < x ==> 2 < x”
end

val _ = tprint "find num->num includes SUC"
val _ = require_msg (check_result (tmem numSyntax.suc_tm))
                    (listp term_to_string)
                    find_consts “:num->num”
val _ = tprint "find 'a includes SUC"
val _ = require_msg (check_result (tmem numSyntax.suc_tm))
                    (listp term_to_string)
                    find_consts “:'a”
val _ = tprint "find 'a->'a includes SUC"
val _ = require_msg (check_result (tmem numSyntax.suc_tm))
                    (listp term_to_string)
                    find_consts “:'a->'a”
val _ = tprint "find 'b->'b includes SUC"
val _ = require_msg (check_result (tmem numSyntax.suc_tm))
                    (listp term_to_string)
                    find_consts “:'b->'b”
val _ = tprint "find 'a -> 'b -> 'c doesn't include SUC"
val _ = require_msg (check_result (not o tmem numSyntax.suc_tm))
                    (listp term_to_string)
                    find_consts “:'a->'b->'c”
val _ = tprint "find_thy [bool,relation] 'a -> 'a doesn't include SUC"
val _ = require_msg (check_result (not o tmem numSyntax.suc_tm))
                    (listp term_to_string)
                    (find_consts_thy ["bool", "relation"]) “:'a->'a”
val _ = tprint "find_thy [bool,relation] 'a -> 'a includes RTC"
val _ = require_msg (check_result (tmem “relation$RTC”))
                    (listp term_to_string)
                    (find_consts_thy ["bool", "relation"]) “:'a->'a”
val _ = tprint "find_thy [bool,relation] num -> num doesn't include RTC"
val _ = require_msg (check_result (not o tmem “relation$RTC”))
                    (listp term_to_string)
                    (find_consts_thy ["bool", "relation"]) “:num->num”

val _ = new_constant("foo", “:'a -> num”)

val _ = tprint "find 'a finds new constant"
val _ = require_msg (check_result (tmem “foo”)) (listp term_to_string)
                    find_consts “:'a”


val _ = new_constant ("split", ``:num list -> (num list # num list) ``)
local
  val quotation = `
  bar Γ =
    case split Γ of
        (Γ1, Γ2) => if EVEN (bar Γ1) then 2 else bar Γ2`

  val mkdef = quietly (Defn.mk_defn "bar")
  fun test q =
      let
        val (tm,_) = Defn.parse_absyn (Parse.Absyn q)
      in
        (mkdef tm, mkdef tm)
      end
  fun is_nested (DefnBase.NESTREC _ ) = true | is_nested _ = false
  fun check_defs (d1,d2) =
      is_nested d1 andalso is_nested d2 andalso
      length (Defn.tcs_of d1) = length (Defn.tcs_of d2)
  val ppd = PP.pp_to_string 65 DefnBase.pp_defn
  fun prdefpair (d1,d2) = ppd d1 ^ "\n   vs\n" ^ ppd d2
in
val _ = tprint "TFL nested recursion + Unicode parameter name"
val _ = require_msg (check_result check_defs) prdefpair test quotation
end

val goalpp =
    HOLPP.pp_to_string 75 (
      HOLPP.block HOLPP.CONSISTENT 0 o
      HOLPP.pr_list goalStack.pp_goal [HOLPP.NL, HOLPP.NL]
    )
fun testtac tac = #1 o runtac (VALID tac)

val _ = let
  val _ = tprint "tmCases_on (.doc file example)"
  val g = ([], “MAP (f:num -> num) l = []”)
  val expected = [([] : term list, “MAP (f:num -> num) [] = []”),
                  ([] : term list , “MAP (f:num -> num) (e::es) = []”)]
in
  require_msg (check_result (list_eq goal_eq expected))
              goalpp
              (testtac (tmCases_on (mk_var("l", alpha)) ["", "e es"]))
              g
end

val _ = let
  val _ = tprint "tmCases_on (bound l)"
  val g = ([], “!l. MAP (f:num -> num) l = []”)
  val expected = [([] : term list, “MAP (f:num -> num) [] = []”),
                  ([] : term list , “MAP (f:num -> num) (e::es) = []”)]
in
  require_msg (check_result (list_eq goal_eq expected))
              goalpp
              (testtac (tmCases_on (mk_var("l", alpha)) ["", "e es"]))
              g
end

val _ = let
  val _ = tprint "resolve_then/IRULE hyp order preserved"
  val th1 = rich_listTheory.is_prefix_el
  val g = ([], “?m n. EL m (l1:'a list) = EL n l2 /\ m <= n /\ EVEN n”)
  val expected =
      [([] : term list,
        “?n. (l1:'a list) <<= l2 /\ n < LENGTH l1 /\ n < LENGTH l2 /\ n <= n /\
             EVEN n”)]
in
  require_msg (check_result (list_eq goal_eq expected))
              goalpp
              (testtac ((goal_assum o resolve_then Any mp_tac) th1))
              g
end

val gstest_goal =
    ([``x <= b``, ``b - x = b - y``, ``y <= b``], ``x * y < 10``);
val _ =
    shouldfail {
      checkexn = check_HOL_ERRexn (fn(_,s2,_) => s2 = "CHANGED_TAC"),
      printarg = fn _ => "fs with ordering failure",
      printresult = goalpp,
      testfn = testtac (CHANGED_TAC (fs [arithmeticTheory.SUB_CANCEL]))
    } gstest_goal

val _ = tprint "gs with ordering works"
val _ = require_msg
          (check_result
             (goals_eq [([“x:num = y”, “y <= b”], “y ** 2 < 10”)]))
          goalpp
          (testtac (gs[arithmeticTheory.SUB_CANCEL]))
          gstest_goal

val _ = tprint "rgs with ordering works"
val _ = require_msg
          (check_result
             (goals_eq [([“y <= b”, “x:num = y”], “y ** 2 < 10”)]))
          goalpp
          (testtac (rgs[arithmeticTheory.SUB_CANCEL]))
          gstest_goal

val _ = tprint "gvs with ordering works"
val _ = require_msg
          (check_result
             (goals_eq [([“x <= b”], “x ** 2 < 10”)]))
          goalpp
          (testtac (gvs[arithmeticTheory.SUB_CANCEL]))
          gstest_goal

(* The case tactics keep their simpset and assumption rewriter between
   calls; a datatype defined after a call must still have its case and
   distinctness theorems applied. *)
val _ = let
  val _ = testtac CASE_TAC ([], “(case l of [] => 0 | h::t => h:num) = 0”)
  val _ = testtac BasicProvers.FULL_CASE_TAC
                  ([“(case l of [] => 0 | h::t => h:num) = m”],
                   “P (m:num) : bool”)
  val _ = Datatype‘casetac_ty = CT1 | CT2 num’
  val _ = tprint "CASE_TAC on a datatype defined after a CASE_TAC call"
in
  require_msg (check_result (goals_eq [([], “n = 0”)]))
              goalpp
              (testtac CASE_TAC)
              ([], “(case x of CT1 => 0 | CT2 n => n) = 0 ∨ x = CT1”)
end

val _ = tprint "FULL_CASE_TAC on a datatype defined after a FULL_CASE_TAC call"
val _ = require_msg
          (check_result (goals_eq [([“0 = m”], “P (m:num) : bool”),
                                   ([“1 = m”], “P (m:num) : bool”)]))
          goalpp
          (testtac BasicProvers.FULL_CASE_TAC)
          ([“(case x of CT1 => 0 | CT2 n => 1) = m”], “P (m:num) : bool”)

val _ = tprint "EVERY_CASE_TAC on a datatype defined later"
val _ = require_msg (check_result (goals_eq [([], “n = 0”)]))
                    goalpp
                    (testtac BasicProvers.EVERY_CASE_TAC)
                    ([], “(case x of CT1 => 0 | CT2 n => n) = 0 ∨ x = CT1”)

(* The case tactics rewrite with the implicit rewrites of the context they
   are given, not those of the live cell: FULL_CASE_TAC on every
   assumption, CASE_TAC on the old assumptions after a split on a
   non-variable. *)
val _ = let
  val plain = Context.snapshot ()
  val _ = Rewrite.add_implicit_rewrites [arithmeticTheory.ADD_0]
  val extra = Context.snapshot ()
  val _ = Context.restore plain
  fun testtac_in c tac g = fst (VALID tac g c)
  val w = “P (k:num) : bool”
  val q = “Q (m:num) : bool”
  val _ = tprint "FULL_CASE_TAC reads the context it is given"
  val _ = require_msg
            (check_result (goals_eq [([“m = k:num”], w), ([“1 = k:num”], w)]))
            goalpp
            (testtac_in extra BasicProvers.FULL_CASE_TAC)
            ([“(case x of CT1 => m + 0 | CT2 n => 1) = k”], w)
  val _ = tprint "CASE_TAC rewrites old assumptions in the context it is given"
in
  require_msg
    (check_result (goals_eq [([“f (y:num) = CT1”, q], “a = c:num”),
                             ([“f (y:num) = CT2 n”, q], “b = c:num”)]))
    goalpp
    (testtac_in extra CASE_TAC)
    ([“Q (m + 0:num) : bool”],
     “(case f (y:num) of CT1 => a | CT2 n => b) = c:num”)
end

(* A datatype declared under a pin has its case rewrites in the pin.  The
   tactics run inside it: TypeBase.dest_case checks constants against the
   live signature, which lacks the pin's. *)
val _ = let
  val expected = [([], “0 = k:num”), ([], “n = k:num”)]
  fun run_pinned (name, tac) = let
    val _ = tprint (name ^ " on a datatype declared under a pin")
    val _ = Datatype‘casetac_pin = CP1 | CP2 num’
    val c = Context.snapshot ()
  in
    require_msg (check_result (goals_eq expected)) goalpp
                (fn g => fst (VALID tac g c))
                ([], “(case z of CP1 => 0 | CP2 n => n) = k:num”)
  end
in
  List.app (fn nt => Context.with_context (Context.snapshot ()) run_pinned nt)
           [("CASE_TAC", CASE_TAC),
            ("TOP_CASE_TAC", BasicProvers.TOP_CASE_TAC)]
end

fun test_tac_Case nm ok_case_arg tq tac = let
  val t = Parse.typed_parse_in_context bool [] tq
  val _ = tprint (nm^" on `"^term_to_string t^"`")
  val (goals, _) = runtac tac ([], t)
  fun ok_case t = ok_case_arg (markerSyntax.dest_Case t)
    handle HOL_ERR _ => false
  fun has_ok_Case (asms, _) = Lib.exists ok_case asms
  val missing = filter (not o has_ok_Case) goals
in
  if null missing
  then OK ()
  else die (int_to_string (length missing) ^ " goals missing Case.\nFAILED!\n")
end handle HOL_ERR _ => die "FAILED (tactic failed)!\n"

val _ = test_tac_Case "list ind" (K true)
  `!xs. NULL xs`
  (recInduct
      (name_ind_cases [] listTheory.list_induction)
    \\ rpt strip_tac)

val _ = test_tac_Case "OLEAST deep intro" (K true)
  `THE (OLEAST n. n > SUC 3) < 8`
  (DEEP_INTRO_TAC
      (name_ind_cases [] WhileTheory.OLEAST_INTRO)
    \\ rpt strip_tac)

val (is_rev_rules, is_rev_ind, is_rev_cases) = Hol_reln`
  (is_rev [] []) /\
  (!x xs ys. is_rev xs ys ==> is_rev (CONS x xs) (SNOC x ys))`;

val _ = test_tac_Case "is_rev rule ind" (K true)
  `!xs ys. is_rev xs ys ==> !zs. is_rev ys zs ==> zs = xs`
  (ho_match_mp_tac
      (name_ind_cases [] is_rev_ind)
    \\ rpt strip_tac)

val f_def = Define`
  f [] = [] /\
  f (x :: xs) = x :: f2 xs /\
  f2 [] = [] /\
  f2 (x :: xs) = x :: f xs`;
val f_ind = theorem "f_ind";

val diff_names_test = let
    val thm = name_ind_cases [F,T] f_ind
    val cases = find_terms (can markerSyntax.dest_Case) (concl thm)
    val ok = length (op_mk_set term_eq cases) = length cases
  in
    if ok then OK () else die "diff_names_test: duplicates"
  end handle HOL_ERR _ => die "diff_names_test: exception"

val _ = test_tac_Case "is_rev rule ind"
  (can (find_term (fn t => same_const T t orelse same_const F t)))
  `(!xs : 'a list. f xs = xs) /\ (!xs : 'a list. f2 xs = xs)`
  (ho_match_mp_tac
      (name_ind_cases [F, T] f_ind)
    \\ rpt strip_tac)

val ss = srw_ss()
val _ = convtest ("standard simp on h::t = []", SIMP_CONV ss [],
                  “h::t = [] : 'a list”, “F”)
val _ = BasicProvers.recreate_sset_at_parentage (parents "list")
val _ = shouldfail {checkexn = fn UNCHANGED => true | _ => false,
                    printarg = K "after setting parents, same raises UNCHANGED",
                    printresult = term_to_string,
                    testfn = rhs o concl o SIMP_CONV (srw_ss()) []}
                   “h::t = [] : 'a list”
val _ = convtest ("adjusted simp_conv on set comprehension",
                  SIMP_CONV (srw_ss()) [],
                  “y IN {x | x < 10}”, “y < 10”)
val _ = convtest ("stored simp_conv still fine on h::t = []", SIMP_CONV ss [],
                  “h::t = [] : 'a list”, “F”)
val _ = tprint "Tactic simp[] on set comprehension"
val _ = require_msg (check_result (aconv “y < 10” o #2 o hd o #1))
                    (term_to_string o #2 o hd o #1)
                    (runtac (simp[])) ([], “y IN {x | x < 10}”)

val _ = tprint "CONG_TAC on a set comprehension with numeral"
val expected = [([]: term list, “c * d = 10n”)]
val _ = require_msg (check_result (goals_eq expected o #1))
                    (goals_toString o #1)
                    (runtac (CONG_TAC NONE))
                    ([], “{n | n < c * d} = {x | x < 10}”);

val _ = hide "f"
val _ = tprint "CONG_TAC with MAP congruence used"
val expected = [([“MEM (x:'a) l2”], “f (x:'a) + 1 = g x”),
                ([], “l1 : 'a list = l2”)]
val _ = require_msg
          (check_result (goals_eq expected o #1))
          (goals_toString o #1)
          (runtac (CONG_TAC NONE))
          ([], “MAP (λa. f a + 1) (l1:'a list) = MAP g (l2:'a list)”);

val _ = tprint "CONG_TAC (SOME 0) = ALL_TAC"
val gt = “x < 10n”
val _ = require_msg
          (check_result (goals_eq [([], gt)] o #1))
          (goals_toString o #1)
          (runtac (CONG_TAC (SOME 0)))
          ([], gt)

val _ = shouldfail {
      checkexn = is_struct_HOL_ERR "bossLib",
      printarg = K "CONG_TAC NONE failure 1",
      printresult = goals_toString o #1,
      testfn = runtac (CONG_TAC NONE)
    } ([], “x < 10n”);

fun goalhc t (sgs, vf) =
    case sgs of
        [(asl, c)] => t ~~ c andalso null asl
      | _ => false
fun prgl (sgs, vf) =
    case sgs of
        [] => "[]"
      | [sg] => PP.pp_to_string 70 goalStack.pp_goal sg
      | _ => "Too many subgoals"

val _ = tprint "simp[] ?- “p ∧ T”"
val _ = require_msg
          (check_result (goalhc “p:bool”))
          prgl
          (runtac (simp []))
          ([], “p ∧ T”)

val _ = tprint "above w/simpset_updates removing"
val _ = require_msg
          (check_result (goalhc “p /\ T”)) prgl
          (runtac (BasicProvers.with_simpset_updates_tac
                     (simpLib.remove_simps ["AND_CLAUSES"])
                     (simp[])))
          ([], “p ∧ T”)

val _ = tprint "Back to original"
val _ = require_msg
          (check_result (goalhc “p:bool”)) prgl
          (runtac (simp[]))
          ([], “p ∧ T”)

(*
val _ = convtest("Original again", SIMP_CONV (srw_ss()) [], “p ∧ T”, “p:bool”)
*)

(* ------------------------------------------------------------------- *)
(* GH #2095: a type nested through list has two size equations.  The    *)
(* package tidies the one the recursion gives -- list_size (\x. x)      *)
(* (MAP sz l) -- into the fold list_size sz l, puts that in the         *)
(* TypeBase, and uses it; <ty>_size_def used to bind the raw one, so    *)
(* citing it in a termination proof shadowed the tidied equation with   *)
(* a form that matches neither goals nor lemmas.                        *)
(* ------------------------------------------------------------------- *)

val _ = Datatype`gh2095tree = Gh2095Node (gh2095tree list)`

local
  fun through_MAP th =
      can (find_term (fn t => is_const t andalso fst (dest_const t) = "MAP"))
          (concl th)
in
val _ = tprint "GH2095: <ty>_size_def is the equation TypeBase holds"
val _ =
    let val named = DB.fetch "-" "gh2095tree_size_def"
        val tidied = #2 (TypeBase.size_of “:gh2095tree”)
    in
      if aconv (concl named) (concl tidied) then OK()
      else die ("bound: " ^ thm_to_string named)
    end

val _ = tprint "GH2095: <ty>_size_def does not go through MAP"
val _ =
    let val named = DB.fetch "-" "gh2095tree_size_def"
    in
      if through_MAP named then die (thm_to_string named) else OK()
    end

val _ = tprint "GH2095: no raw size equation is left behind"
val _ =
    case Lib.total (DB.fetch "-") "gh2095tree_size_orig_def" of
        NONE => OK()
      | SOME th => die ("still bound: " ^ thm_to_string th)

val _ = tprint "GH2095: <ty>_size_def is still one of the definitions"
val _ =
    case Lib.total definition "gh2095tree_size_def" of
        NONE => die "not a definition of the segment"
      | SOME _ => OK()

val _ = tprint "GH2095: the userdef query gives the tidied equation"
val _ =
    let
      fun eqn (DefnBase.STDEQNS th) = th
        | eqn (DefnBase.OTHER th) = th
    in
      case DefnBase.lookup_userdef (#1 (TypeBase.size_of “:gh2095tree”)) of
          NONE => die "no userdef registered for the size constant"
        | SOME p =>
          let val th = eqn (#thm p)
          in
            if through_MAP th then die (thm_to_string th) else OK()
          end
    end
end

(* ------------------------------------------------------------------- *)
(* A type that recurses under an operator has its recursion axiom       *)
(* stated with that operator's map, so new_recursive_definition can     *)
(* only match a recursive call that is the function itself.  A call     *)
(* given arguments ahead of the recursive one cannot be put in that     *)
(* form -- canonising it moves them under the map.  The clause it       *)
(* could not match used to be left assumed, and the complaint came      *)
(* from new_specification, several layers down, that a theorem it was   *)
(* handed had assumptions.                                              *)
(* ------------------------------------------------------------------- *)

val _ = Datatype`prtree = PRLeaf | PRNode (prtree list)`

local
  fun attempt def =
      Prim_rec.new_recursive_definition
        {name = "prbad_def", rec_axiom = TypeBase.axiom_of “:prtree”,
         def = def}
  fun outcome def = (ignore (attempt def); NONE)
                    handle Feedback.HOL_ERR e => SOME e
in
val _ = tprint "a recursive call under a map that is not the function"
val _ =
    case outcome “(prbad (f:num -> num) PRLeaf = 0) /\
                  (prbad f (PRNode l) = SUM (MAP (prbad f) l))” of
        NONE => die "the definition was accepted"
      | SOME e =>
        if Feedback.top_function_of e = "new_recursive_definition" andalso
           String.isSubstring "recursion axiom" (Feedback.message_of e)
        then OK()
        else die (Feedback.message_of e)
end

(* ------------------------------------------------------------------- *)
(* GH #2098: TFL eta-expands a call that supplies a function too few    *)
(* arguments, and that expansion used to survive into the saved         *)
(* equation.  Unfolding a definition recursing through MAP or EVERY     *)
(* then gave MAP (\a. g n a) ts where MAP (g n) ts was written, which   *)
(* matches neither goals nor lemmas stated the way they were written.   *)
(* The primitive-recursive case must be left exactly as it was.         *)
(* ------------------------------------------------------------------- *)

val _ = Datatype`etatree = Nd (etatree list) | Lf`;

local
  (* an abstraction \x. t x with x not free in t says nothing that t
     does not; the defect is that extraction leaves these behind *)
  fun eta_redex tm =
      case Lib.total dest_abs tm of
          NONE => false
        | SOME (v, bdy) =>
          (case Lib.total dest_comb bdy of
               NONE => false
             | SOME (rator, rand) =>
               aconv rand v andalso not (free_in v rator))
  fun eta_free th = not (can (find_term eta_redex) (concl th))
  fun mentions pat th = can (find_term (aconv pat)) (concl th)
  fun check (pat, th) = eta_free th andalso mentions pat th
  fun show (pat, th) =
      "expected " ^ term_to_string pat ^ " in " ^ thm_to_string th
in
val _ = quietly Define`etaf (Nd ts) = Nd (MAP etaf ts) /\ etaf Lf = Lf`;
val _ = quietly Define`
  etag (n:num) (Nd ts) = Nd (MAP (etag n) ts) /\ etag n Lf = Lf`;
val _ = quietly Define`etap (Nd ts) = EVERY etap ts /\ etap Lf = T`;
val _ = quietly Define`
  etaq (n:num) (Nd ts) = EVERY (etaq n) ts /\ etaq n Lf = T`;

val _ = tprint "GH2098: primitive recursion through MAP (unchanged)"
val _ = require_msg (check_result check) show (fn x => x)
                    (“MAP etaf”, DB.fetch "-" "etaf_def")

val _ = tprint "GH2098: TFL recursion through MAP, partially applied"
val _ = require_msg (check_result check) show (fn x => x)
                    (“MAP (etag n)”, DB.fetch "-" "etag_def")

val _ = tprint "GH2098: TFL recursion through EVERY, bare call"
val _ = require_msg (check_result check) show (fn x => x)
                    (“EVERY etap”, DB.fetch "-" "etap_def")

val _ = tprint "GH2098: TFL recursion through EVERY, partially applied"
val _ = require_msg (check_result check) show (fn x => x)
                    (“EVERY (etaq n)”, DB.fetch "-" "etaq_def")
end

(* ------------------------------------------------------------------- *)
(* GH #2108: an operator-wise principle where the operator is one a     *)
(* declaration defined, and collects what it holds through operators    *)
(* of its own.  `envSET` says                                           *)
(*                                                                      *)
(*   envSET (env a0 a1) = BIGUNION (IMAGE setSND (set a0))              *)
(*                                                                      *)
(* so the values are reached through a list and then a pair, and the    *)
(* stated principle mentions neither -- `env` is an operator in its own *)
(* right and its contents are what `envSET` collects.  The older        *)
(* construction gave the list and the pair a predicate apiece, and this *)
(* is that principle.  (A real list is wanted, so this cannot live in   *)
(* src/datatype, which has a list of its own.)                          *)
(* ------------------------------------------------------------------- *)

val _ = Datatype`gh2108env = <| ve : (num # 'a) list ; vn : num |>`
val _ = Datatype`gh2108v = G8C (gh2108v gh2108env) | G8N num`

val _ = tprint "GH2108: the older shape through an operator's own operators"
val _ =
    let
      fun same t1 t2 = can (match_term t1) t2 andalso can (match_term t2) t1
      val th = legacyInduction.mutual_ind_from_ops
                 (TypeBase.set_induction_of “:gh2108v”)
    in
      if same (concl th)
           “∀P Q0 Q1 Q2.
              (∀e. Q0 e ⇒ P (G8C e)) ∧ (∀n. P (G8N n)) ∧
              (∀l n. Q1 l ⇒ Q0 (gh2108env l n)) ∧ Q1 [] ∧
              (∀t h. Q2 h ∧ Q1 t ⇒ Q1 (h::t)) ∧
              (∀p_1 p_2. P p_2 ⇒ Q2 (p_1,p_2)) ⇒
              (∀v. P v) ∧ (∀e. Q0 e) ∧ (∀l. Q1 l) ∧ ∀p. Q2 p”
      then OK() else die ("not the older shape: " ^ thm_to_string th)
    end

(* and the commonest case of all, which comes by the same route *)
val _ = Datatype`gh2108lt = G8LNil | G8LRec (gh2108lt list)`

val _ = tprint "GH2108: a plain list operator still comes out right"
val _ =
    let
      fun same t1 t2 = can (match_term t1) t2 andalso can (match_term t2) t1
      val th = legacyInduction.mutual_ind_from_ops
                 (TypeBase.set_induction_of “:gh2108lt”)
    in
      if same (concl th)
           “∀P Q0. P G8LNil ∧ (∀l. Q0 l ⇒ P (G8LRec l)) ∧ Q0 [] ∧
                   (∀t h. P h ∧ Q0 t ⇒ Q0 (h::t)) ⇒
                   (∀l. P l) ∧ ∀l. Q0 l”
      then OK() else die ("not the older shape: " ^ thm_to_string th)
    end

(* ------------------------------------------------------------------- *)
(* GH #2097: a nested type's induction hypotheses.  With nothing tagged *)
(* to datatype_simp the principle is rephrased only -- the existentials *)
(* the chain leaves are pulled out and the equalities that leaves are   *)
(* unwound.  A development says what more it wants by tagging theorems. *)
(* The principle as the construction stated it stays available, because *)
(* code reads that one and a development may tag anything.             *)
(* ------------------------------------------------------------------- *)

val _ = Datatype`gh2097exp = G7Var num
                           | G7Rec ((num # gh2097exp) list) gh2097exp
                           | G7Raise (gh2097exp option)`

local
  fun hasEx th = can (find_term is_exists) (concl th)
in
val _ = tprint "GH2097: the chain's existentials are pulled out"
val _ =
    let val th = DB.fetch "-" "gh2097exp_induction"
    in if hasEx th then die (thm_to_string th) else OK() end

val _ = tprint "GH2097: the stated principle is kept beside it"
val _ =
    let val th = TypeBase.set_induction_of “:gh2097exp”
    in
      if hasEx th then OK() else die ("no existential: " ^ thm_to_string th)
    end

end

val _ = tprint "GH2097: a tagged theorem reaches a later declaration"
val _ =
    let
      val before_ = length (datatypeSimpLib.datatype_simps())
      val _ = List.app datatypeSimpLib.add_datatype_simp
                ["pair.setSND_def", "pred_set.IN_ABS", "pair.FORALL_PROD",
                 "pair.SND", "bnfPrelims.IN_optSET"]
      val _ = Datatype`gh2097b = G7bNil | G7bRec ((num # gh2097b) list)`
      val th = DB.fetch "-" "gh2097b_induction"
      val after = length (datatypeSimpLib.datatype_simps())
    in
      if after <= before_ then die "nothing was tagged"
      else if can (find_term (fn t => is_const t andalso
                                      #1 (dest_const t) = "setSND"))
                  (concl th)
      then die ("setSND survived: " ^ thm_to_string th)
      else OK()
    end
