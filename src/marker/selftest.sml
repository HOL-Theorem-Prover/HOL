open HolKernel Parse boolLib testutils markerLib

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
