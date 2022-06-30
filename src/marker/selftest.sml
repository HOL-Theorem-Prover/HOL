open HolKernel Parse boolLib testutils markerLib

val _ = set_trace "Unicode" 0

fun testtac tac = #1 o VALID tac
val goalprint =
    HOLPP.pp_to_string 75(
      HOLPP.block HOLPP.CONSISTENT 0 o
      HOLPP.pr_list goalStack.pp_goal [HOLPP.NL, HOLPP.NL]
    )

val L12_asms = [“L1 :- (x:'a) = a”, “L2 :- (y:'a) = b”]
val _ = tprint "LLABEL_RES_THEN(1)"
val _ = require_msg
      (check_result (goals_eq [(L12_asms, “(a:'a) = y”)]))
      goalprint
      (testtac (LLABEL_RES_THEN ASM_REWRITE_TAC [L"L1"]))
      (L12_asms, “x:'a = y”)

val _ = tprint "LLABEL_RES_THEN(2)"
val _ = require_msg
      (check_result (goals_eq [(L12_asms, “(a:'a) = b”)]))
      goalprint
      (testtac (LLABEL_RES_THEN ASM_REWRITE_TAC [L"L1", L"L2"]))
      (L12_asms, “x:'a = y”)

val _ = tprint "LLABEL_RES_THEN(3)"
val _ = require_msg
      (check_result (goals_eq [(L12_asms, “(x:'a) = y”)]))
      goalprint
      (testtac (LLABEL_RES_THEN ASM_REWRITE_TAC []))
      (L12_asms, “x:'a = y”)

val _ = tprint "LLABEL_RES_THEN(4)"
val _ = require_msg
      (check_result (goals_eq [(“y:'a = c” :: L12_asms, “(x:'a) = c”)]))
      goalprint
      (testtac (LLABEL_RES_THEN ASM_REWRITE_TAC []))
      (“y:'a = c ” :: L12_asms, “x:'a = y”)

val _ = tprint "LLABEL_RES_THEN(5)"
val _ = require_msg
      (check_result (goals_eq [(“y:'a = c” :: L12_asms, “(x:'a) = c”)]))
      goalprint
      (testtac (LLABEL_RES_THEN REWRITE_TAC [ASSUME “y:'a = c”]))
      (“y:'a = c” :: L12_asms, “x:'a = y”)

val _ = tprint "LLABEL_RES_THEN(6)"
val _ = require_msg
      (check_result (goals_eq [(“y:'a = c” :: L12_asms, “(a:'a) = c”)]))
      goalprint
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
          (trace ("types", 1) goalprint)
          (testtac (RULE_ASSUM_TAC (REWRITE_RULE[])))
          (asl0, “Q c1 c2:bool”)

val _ = tprint "SUBST_ALL_TAC doesn't hit hide"
val tyopEQ = new_axiom("tyopEQ", “c1:tyop = c2”);
val _ = require_msg
          (check_result (goals_eq [([“hide foo (P c1 /\ T /\ P x)”,
                                     “R c2 /\ T /\ R x”],
                                    “Q c2 c2:bool”)]))
          (trace ("types", 1) goalprint)
          (testtac (SUBST_ALL_TAC tyopEQ))
          (asl0, “Q c1 c2:bool”)

val _ = tprint "SUBST_ALL_TAC/CONJ_VALIDATE doesn't hit hide"
val _ = require_msg
          (check_result (goals_eq [(asl0, “x = c1”),
                                   ([“hide foo (P c1 /\ T /\ P x)”,
                                     “R c1 /\ T /\ R c1”],
                                    “Q c1 c2:bool”)]))
          (trace ("types", 1) goalprint)
          (testtac (CONJ_VALIDATE (SUBST_ALL_TAC (ASSUME “x = c1”))))
          (asl0, “Q c1 c2:bool”)

val _ = tprint "RULE_ASSUM_TAC hits unignored hide"
val _ = require_msg
          (check_result (goals_eq [([“hide foo (P c1 /\ P x)”,
                                     “R c1 /\ R x”],
                                    “Q c1 c2:bool”)]))
          (trace ("types", 1) goalprint)
          (testtac $ unignoring_hide $ RULE_ASSUM_TAC $ REWRITE_RULE[])
          (asl0, “Q c1 c2:bool”)

val _ = new_constant("TEST", “:tyop -> bool”)
val condrwt = new_axiom("condrwt", “!x. TEST x ==> x = c1”);
val crwt = MATCH_MP condrwt (ASSUME “TEST y”)
val _ = tprint "CONJ_VALIDATE(1)"
val _ = require_msg
          (check_result (goals_eq[([], “TEST y /\ P c1”)]))
          (trace ("types", 1) goalprint)
          (testtac (CONJ_VALIDATE (REWRITE_TAC[crwt])))
          ([], “P (y:tyop):bool”)
