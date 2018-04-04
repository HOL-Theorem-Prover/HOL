open HolKernel Parse goalStack Tactic Tactical
open testutils

val _ = set_trace "Unicode" 0

val _ = tprint "test of flatn"
val _ = goalStack.chatting := false

val _ = let
    val g = ([], ``a ==> b ==> c ==> d ==> e ==> a /\ b /\ c /\ d /\ e``) : goal
    val gstk = new_goal g Lib.I ;
    val gstk = expand (REPEAT DISCH_TAC) gstk ;
    val gstk = expand (REVERSE CONJ_TAC) gstk ;
    val gstk = expand (REVERSE CONJ_TAC) gstk ;
    val gstk = expand (REVERSE CONJ_TAC) gstk ;
    val gstk = expand (REVERSE CONJ_TAC) gstk ;
    val gstk = expand ALL_TAC gstk  ; val 1 = length (top_goals gstk) ;
    val gstk = flatn gstk 2 ; val 3 = length (top_goals gstk) ;
    val gstk = flatn gstk 2 ; val 5 = length (top_goals gstk) ;
    val gstk = flatn gstk 2 ; val 5 = length (top_goals gstk) ;
    val gstk = expand_list (ALLGOALS (FIRST_ASSUM ACCEPT_TAC)) gstk ;
    val th = extract_thm gstk ;
  in if (hyp th, concl th) = g then OK() else die "FAILED" end ;

fun mkstk0 t tacopt =
  let
    open goalStack
    val g0 = new_goal ([], t) (fn x => x)
  in
    case tacopt of
        NONE => g0
      | SOME t => expand t g0
  end

fun mkstk t = mkstk0 t (SOME (rpt strip_tac))

val _ = set_trace "Goalstack.other_subgoals_pretty_limit" 5

val _ = current_backend := PPBackEnd.vt100_terminal;

fun blue s = "\027[0;1;34m" ^ s ^ "\027[0m"
fun stksfx n = "\n\n\n" ^ Int.toString n ^ " subgoals"

fun goalstr slist =
  "\n" ^ String.concatWith "\n\n\n\n" (map blue (List.rev slist)) ^
  stksfx (length slist)

fun rawstr slist =
  case slist of
      [] => raise Fail "Can't happen"
    | h::t => "\n" ^ String.concatWith "\n\n\n\n" (List.rev t @ [blue h]) ^
              stksfx (length slist)

fun mkgstkstr strings =
  let
    val t = boolSyntax.list_mk_conj (map(fn s => mk_var(s,bool)) strings)
    val gstk = with_flag (goalStack.chatting, false) mkstk t
  in
    HOLPP.pp_to_string 70 goalStack.pp_gstk gstk
  end

fun test nm pred s =
  let
    val _ = tprint nm
    val strings = map str (explode s)
    val expected = pred strings
    val got = mkgstkstr strings
  in
    if got = expected then OK()
    else die ("\nExpected: " ^ String.toString expected ^
              "\nGot     : " ^ String.toString got)
  end

val _ = test "Stack printing; small stack" goalstr "abcde"
val _ = test "Stack printing; big stack" rawstr "abcdefg"

fun narrow_uni_off f =
  HOLPP.pp_to_string 50
       (f |> with_flag (Parse.current_backend, PPBackEnd.raw_terminal)
          |> trace ("Unicode", 0))

val ppgstk = narrow_uni_off goalStack.pp_gstk

fun mkgstkstr t =
  let
    val gstk = with_flag (goalStack.chatting, false) mkstk t
  in
    ppgstk gstk
  end

fun mkg0 t = ppgstk (mkstk0 t NONE)

fun mkprfs t =
    let
      open Manager
      val prfs0 = PRFS []
      val p = new_goalstack ([], t) (fn x => x)
      val prfs = add p prfs0
    in
      narrow_uni_off pp_proofs prfs
    end

fun testf(nm, t, mk, expected) =
  let
    val _ = tprint nm
    val gstr = mk t
  in
    if expected = gstr then OK()
    else die ("\nFAILED: got:\n\"" ^ String.toString gstr ^ "\"\n" ^
              "Expected:\n\"" ^ String.toString expected ^ "\"\n")
  end

val _ = List.app testf [
("Stack printing; breaks in multiple assumptions",
 ``(P a b ==> !x y z. Q a x /\ R b y (f z) ==> R2 (ggg a b x y)) /\
   P (f a) (hhhh b) ==>
     R2 (ggg (hhhh a) b c dd)``, mkgstkstr,
 "\n\n\
 \R2 (ggg (hhhh a) b c dd)\n\
 \------------------------------------\n\
 \  0.  P a b ==>\n\
 \      !x y z.\n\
 \          Q a x /\\ R b y (f z) ==>\n\
 \          R2 (ggg a b x y)\n\
 \  1.  P (f a) (hhhh b)"),
("Stack printing; more than 10 assumptions",
 ``p1 /\ p2 /\ p3 /\ p4 /\ p5 /\ p6 /\ p7 /\ p8 /\ p9 /\ p10 /\ p11 ==> q``,
 mkgstkstr,
 "\n\n\
 \q\n\
 \------------------------------------\n\
 \  0.  p1\n\
 \  1.  p2\n\
 \  2.  p3\n\
 \  3.  p4\n\
 \  4.  p5\n\
 \  5.  p6\n\
 \  6.  p7\n\
 \  7.  p8\n\
 \  8.  p9\n\
 \  9.  p10\n\
 \ 10.  p11"),
("Stack printing; initial goal", ``p /\ q ==> p``, mkg0,
 "Initial goal:\n\
 \\n\
 \\n\
 \p /\\ q ==> p\n"),
("Proofs printing; initial goal", ``p /\ q``, mkprfs,
 "Proof manager status: 1 proof.\n\
 \1. Incomplete goalstack:\n\
 \     Initial goal:\n\
 \     \n\
 \     p /\\ q\n\
 \     \n\
 \     ")
]
