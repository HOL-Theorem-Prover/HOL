open HolKernel Parse boolLib testutils markerLib

val _ = set_trace "Unicode" 0

fun testtac tac = #1 o VALID tac
val goal_print = HOLPP.pp_to_string 75 goalStack.pp_goal

val goals_print =
    HOLPP.pp_to_string 75(
      HOLPP.block HOLPP.CONSISTENT 0 o
      HOLPP.pr_list goalStack.pp_goal [HOLPP.NL, HOLPP.NL]
    )

val L12_asms = [“L1 :- (x:'a) = a”, “L2 :- (y:'a) = b”]
val _ = tprint "LLABEL_RES_THEN(1)"
val _ = require_msg
      (check_result (goals_eq [(L12_asms, “(a:'a) = y”)]))
      goals_print
      (testtac (LLABEL_RES_THEN ASM_REWRITE_TAC [L"L1"]))
      (L12_asms, “x:'a = y”)

val _ = tprint "LLABEL_RES_THEN(2)"
val _ = require_msg
      (check_result (goals_eq [(L12_asms, “(a:'a) = b”)]))
      goals_print
      (testtac (LLABEL_RES_THEN ASM_REWRITE_TAC [L"L1", L"L2"]))
      (L12_asms, “x:'a = y”)

val _ = tprint "LLABEL_RES_THEN(3)"
val _ = require_msg
      (check_result (goals_eq [(L12_asms, “(x:'a) = y”)]))
      goals_print
      (testtac (LLABEL_RES_THEN ASM_REWRITE_TAC []))
      (L12_asms, “x:'a = y”)

val _ = tprint "LLABEL_RES_THEN(4)"
val _ = require_msg
      (check_result (goals_eq [(“y:'a = c” :: L12_asms, “(x:'a) = c”)]))
      goals_print
      (testtac (LLABEL_RES_THEN ASM_REWRITE_TAC []))
      (“y:'a = c ” :: L12_asms, “x:'a = y”)

val _ = tprint "LLABEL_RES_THEN(5)"
val _ = require_msg
      (check_result (goals_eq [(“y:'a = c” :: L12_asms, “(x:'a) = c”)]))
      goals_print
      (testtac (LLABEL_RES_THEN REWRITE_TAC [ASSUME “y:'a = c”]))
      (“y:'a = c” :: L12_asms, “x:'a = y”)

val _ = tprint "LLABEL_RES_THEN(6)"
val _ = require_msg
      (check_result (goals_eq [(“y:'a = c” :: L12_asms, “(a:'a) = c”)]))
      goals_print
      (testtac (LLABEL_RES_THEN REWRITE_TAC [ASSUME “y:'a = c”, L"L1"]))
      (“y:'a = c” :: L12_asms, “x:'a = y”)

val _ = new_type ("tyop", 0);
val _ = new_constant("c1", “:tyop”)
val _ = new_constant("c2", “:tyop”)
val _ = overload_on ("hide", “marker$hide”);
val asl0 = [“hide foo (P c1 /\ T /\ P x)”,
            “R c1 /\ T /\ R x”]
val _ = tprint "RULE_ASSUM_TAC doesn't hit hide"
val _ = require_msg
          (check_result (goals_eq [([“hide foo (P c1 /\ T /\ P x)”,
                                     “R c1 /\ R x”],
                                    “Q c1 c2:bool”)]))
          (trace ("types", 1) goals_print)
          (testtac (RULE_ASSUM_TAC (REWRITE_RULE[])))
          (asl0, “Q c1 c2:bool”)

val _ = tprint "SUBST_ALL_TAC doesn't hit hide"
val tyopEQ = new_axiom("tyopEQ", “c1:tyop = c2”);
val _ = require_msg
          (check_result (goals_eq [([“hide foo (P c1 /\ T /\ P x)”,
                                     “R c2 /\ T /\ R x”],
                                    “Q c2 c2:bool”)]))
          (trace ("types", 1) goals_print)
          (testtac (SUBST_ALL_TAC tyopEQ))
          (asl0, “Q c1 c2:bool”)

val _ = tprint "SUBST_ALL_TAC/CONJ_VALIDATE doesn't hit hide"
val _ = require_msg
          (check_result (goals_eq [(asl0, “x = c1”),
                                   ([“hide foo (P c1 /\ T /\ P x)”,
                                     “R c1 /\ T /\ R c1”],
                                    “Q c1 c2:bool”)]))
          (trace ("types", 1) goals_print)
          (testtac (CONJ_VALIDATE (SUBST_ALL_TAC (ASSUME “x = c1”))))
          (asl0, “Q c1 c2:bool”)

val _ = tprint "RULE_ASSUM_TAC hits unignored hide"
val _ = require_msg
          (check_result (goals_eq [([“hide foo (P c1 /\ P x)”,
                                     “R c1 /\ R x”],
                                    “Q c1 c2:bool”)]))
          (trace ("types", 1) goals_print)
          (testtac $ unignoring_hide $ RULE_ASSUM_TAC $ REWRITE_RULE[])
          (asl0, “Q c1 c2:bool”)

val _ = new_constant("TEST", “:tyop -> bool”)
val condrwt = new_axiom("condrwt", “!x. TEST x ==> x = c1”);
val crwt = MATCH_MP condrwt (ASSUME “TEST y”)
val _ = tprint "CONJ_VALIDATE(1)"
val _ = require_msg
          (check_result (goals_eq[([], “TEST y /\ P c1”)]))
          (trace ("types", 1) goals_print)
          (testtac (CONJ_VALIDATE (REWRITE_TAC[crwt])))
          ([], “P (y:tyop):bool”)

fun thm_eq (hyps,t) th =
    HOLset.equal(hyps, hypset th) andalso t ~~ concl th

fun mklab s t = mk_comb(mk_comb(“suspendlabel”, mk_var(s, “:ind”)), t)
val rhyp = mklab "r" “suspendimp p (suspendimp q r)”
val shyp = mklab "s" “suspendimp p (suspendimp q s)”
val rshyp = mklab "r" “suspendimp p (suspendimp q s)”
val p = mk_var("p", bool)
val q = mk_var("q", bool)

val _ = tprint "suspend (1)"
val _ = require_msg
          (check_result
             (thm_eq (
                 HOLset.fromList Term.compare [rhyp, shyp],
                 “p /\ q ==> r /\ s”)
             )
          )
          thm_to_string
          (fn tac => TAC_PROOF(([], “p /\ q ==> r /\ s”), tac))
          (rpt strip_tac >- suspend "r" >- suspend "s")

val _ = tprint "suspend (2)"
val _ = require_msg
          (check_result
             (thm_eq (
                 HOLset.fromList Term.compare [rshyp, rhyp],
                 “p /\ q ==> r /\ s”)
             )
          )
          thm_to_string
          (fn tac => TAC_PROOF(([], “p /\ q ==> r /\ s”), tac))
          (rpt strip_tac >- suspend "r" >- suspend "r")

val pq_th1 =
    TAC_PROOF(([], “p /\ q ==> q /\ p”),
              strip_tac >> conj_tac >- suspend "q" >- suspend "p")
val pq_th2 =
    TAC_PROOF(([], “p /\ q ==> q /\ p”),
              strip_tac >> conj_tac >> suspend "pq")

val _ = tprint "extract_suspended_goal (1)"
val _ = require_msg
          (check_result (goal_eq ([q, p], p)))
          goal_print
          (fn th => resumption_to_goal (extract_suspended_goal th "p"))
          pq_th1

val _ = tprint "extract_suspended_goal (2)"
val _ = require_msg
          (check_result (
              goal_eq (
                [],
                “resconj (suspendimp p (suspendimp q p))
                         (suspendimp p (suspendimp q q))”
              )
            )
          )
          goal_print
          (fn th => resumption_to_goal (extract_suspended_goal th "pq"))
          pq_th2

val _ = shouldfail {checkexn = is_struct_HOL_ERR "markerLib",
                    printarg = K "extract_suspended_goal fails (1)",
                    printresult = goal_print,
                    testfn = (fn th => resumption_to_goal
                                         (extract_suspended_goal th "pq"))}
                   pq_th1

val _ = show_assums := true
val _ = tprint "prim_resume (1a)"
fun pp {subresult,updated_main} =
    let open HOLPP
    in
      PrettyBlock(0,true,[],[
                    pp_thm subresult,
                    PrettyLineBreak,
                    pp_thm updated_main
                    ])
    end
fun one_b (Res {subresult,updated_main}) = (
  tprint "prim_resume (1b)";
  require_msg(check_result
                (fn {subresult,updated_main} =>
                    thm_eq (HOLset.fromList Term.compare [q], q)
                           subresult
                    andalso
                    thm_eq (HOLset.empty Term.compare, “p /\ q ==> q /\ p”)
                           updated_main))
             (HOLPP.pp_to_string 75 pp)
             (fn th => prim_resume (th, "q", first_assum ACCEPT_TAC))
             updated_main
)
  | one_b (Exn _) = die "Shouldn't happen in test"
val _ = require_msgk (check_result
                        (fn {subresult,updated_main} =>
                            thm_eq (HOLset.fromList Term.compare [p],p)
                                   subresult andalso
                            thm_eq (HOLset.fromList Term.compare [
                                       mk_comb(“suspendlabel q”,
                                                “suspendimp p (suspendimp q q)”)
                                     ],
                                    “p /\ q ==> q /\ p”) updated_main))
                     pp
                     (fn th => prim_resume(th,"p",first_assum ACCEPT_TAC))
                     one_b
                     pq_th1

val incomplete_th = Feedback.quiet_messages save_thm("incomplete_th", pq_th1)
val _ = shouldfail {
      checkexn = is_struct_HOL_ERR "Theory",
      printarg = K "export_theory fails on incomplete suspension",
      printresult = K "()",
      testfn = export_theory} ()
val _ = boolLib.remove_suspension "incomplete_th"
