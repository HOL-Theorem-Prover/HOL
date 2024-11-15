open HolKernel Parse boolLib bossLib DB
open testutils

val _ = print "\n"

fun listprint pr xs =
    "[" ^ String.concatWith "," (map pr xs) ^ "]"


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
    handle HOL_ERR {origin_function, message, origin_structure, ...} =>
           if origin_function <> "new_type_definition" orelse
              origin_structure <> "Theory.Definition" orelse
              message <> "at Thm.prim_type_definition:\nexpected a theorem of the form \"?x. P x\""
           then
             die "FAILED"
           else OK()

val _ = tprint "Q.MATCH_ABBREV_TAC with underscores"
val goal = ([] : term list, ``(n + 10) * y <= 42315 /\ !x y:'a. x < f y``)
val (sgs, _) = Q.MATCH_ABBREV_TAC `a * _ <= b /\ _` goal
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
val (sgs, _) = qhdtm_x_assum `FACT` mp_tac goal
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
                (match1_tac test1 g1)

val test2 =
  [
    ([mg.abc `if b_ then _ else _`],
     fn (t,a) => (Cases_on`^(a"b")`))
    ,([],(K ALL_TAC):mg_tactic)
  ]

val res1' = test_assert (goals_eq [g1] o #1) (first_match_tac test2 g1)

val g2 = ([``x:bool = if P then x' else x''``, ``x:bool``],``yi = if x then x'' else (ARB:bool)``)

val res2 = test_assert (equal 2 o length o #1)
  (first_match_tac test2 g2)

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
  (match_tac test3 g3)

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
  (match_tac test4 g4)

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
                    (listprint term_to_string)
                    find_consts “:num->num”
val _ = tprint "find 'a includes SUC"
val _ = require_msg (check_result (tmem numSyntax.suc_tm))
                    (listprint term_to_string)
                    find_consts “:'a”
val _ = tprint "find 'a->'a includes SUC"
val _ = require_msg (check_result (tmem numSyntax.suc_tm))
                    (listprint term_to_string)
                    find_consts “:'a->'a”
val _ = tprint "find 'b->'b includes SUC"
val _ = require_msg (check_result (tmem numSyntax.suc_tm))
                    (listprint term_to_string)
                    find_consts “:'b->'b”
val _ = tprint "find 'a -> 'b -> 'c doesn't include SUC"
val _ = require_msg (check_result (not o tmem numSyntax.suc_tm))
                    (listprint term_to_string)
                    find_consts “:'a->'b->'c”
val _ = tprint "find_thy [bool,relation] 'a -> 'a doesn't include SUC"
val _ = require_msg (check_result (not o tmem numSyntax.suc_tm))
                    (listprint term_to_string)
                    (find_consts_thy ["bool", "relation"]) “:'a->'a”
val _ = tprint "find_thy [bool,relation] 'a -> 'a includes RTC"
val _ = require_msg (check_result (tmem “relation$RTC”))
                    (listprint term_to_string)
                    (find_consts_thy ["bool", "relation"]) “:'a->'a”
val _ = tprint "find_thy [bool,relation] num -> num doesn't include RTC"
val _ = require_msg (check_result (not o tmem “relation$RTC”))
                    (listprint term_to_string)
                    (find_consts_thy ["bool", "relation"]) “:num->num”

val _ = new_constant("foo", “:'a -> num”)

val _ = tprint "find 'a finds new constant"
val _ = require_msg (check_result (tmem “foo”)) (listprint term_to_string)
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
fun testtac tac = #1 o VALID tac

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

fun test_tac_Case nm ok_case_arg tq tac = let
  val t = Parse.typed_parse_in_context bool [] tq
  val _ = tprint (nm^" on `"^term_to_string t^"`")
  val (goals, _) = tac ([], t)
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
      (name_ind_cases [] whileTheory.OLEAST_INTRO)
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
                    (simp[]) ([], “y IN {x | x < 10}”)
