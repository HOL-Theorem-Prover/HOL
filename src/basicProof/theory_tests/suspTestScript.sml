Theory suspTest[bare]

(* Tests suspension and resumption with and without "modern syntax" for
   the various steps (Theorem (with suspend tactic), Resume, and Finalise).
*)

Libs HolKernel Parse boolLib markerLib BasicProvers Q[qualified]

fun simp ths = simpLib.asm_simp_tac (srw_ss()) ths
fun SCONV ths = simpLib.SIMP_CONV (srw_ss()) ths

Theorem willsplit:
  p ∧ (p ⇒ q) ⇒ p ∧ q
Proof
  strip_tac >> conj_tac
  >- suspend "p"
  >- suspend "q"
QED

Theorem willsplit2:
  p ∧ ~p ⇒ q
Proof
  (* strip_tac is too smart and just proves this outright *)
  disch_then (CONJUNCTS_THEN assume_tac) >> suspend "q"
QED

val _ = set_suspended_goal {
  label_name = "p", suspension_name = "willsplit"}

val psubgoal = resume{label_name = "p", suspension_name = "willsplit"}
  (ASM_REWRITE_TAC[])

val _ = set_suspended_goal {
  label_name = "q", suspension_name = "willsplit"}

Resume willsplit[q]:
  RES_TAC
QED

Resume willsplit2[q,smlname=q2sg]:
  SUFF_TAC “F” THENL [REWRITE_TAC[], suspend "q"]
QED

val c = concl q2sg;

val _ = set_suspended_goal {
  label_name = "q", suspension_name = "willsplit2"
  }

val q3sg = resume{label_name = "q", suspension_name = "willsplit2"}
  (RES_TAC)

val willsplit2 = finalise_suspended_thm (DB_dtype.mkloc(#(FILE),#(LINE),true))
                                   "willsplit2"
val final = finalise_suspended_thm (DB_dtype.mkloc(#(FILE),#(LINE),true))
                                   "willsplit"

val ws = fetch "suspTest" "willsplit"
val ws2 = fetch "suspTest" "willsplit2"

Theorem multisplit:
  p ∧ q ⇒ q ∧ p
Proof
  rpt strip_tac >> suspend "p"
QED

val _ = set_suspended_goal
  {label_name = "p", suspension_name = "multisplit"}

val multi_resumed = resume{label_name = "p", suspension_name = "multisplit"}
  (RESUME_TAC >> FIRST_ASSUM ACCEPT_TAC)

Finalise multisplit

val ms = fetch "suspTest" "multisplit"

Theorem testTacMod:
  p ∧ q ⇒ q ∧ (p ∧ p)
Proof
  strip_tac >> suspend "rtp_qpp"
QED

Resume testTacMod[rtp_qpp,exclude_simps=AND_CLAUSES]:
  TRY (simp[] >> NO_TAC) >>
  simp[] >> rpt conj_tac >> ACCEPT_TAC TRUTH
QED

Finalise testTacMod

Theorem testFinalEqn:
  p ∧ T ∧ q <=> p ∧ q
Proof
  iff_tac >- suspend "l2r" >- suspend "r2l"
QED

Resume testFinalEqn[l2r]:
  simp[]
QED

Resume testFinalEqn[r2l]:
  simp[]
QED

Finalise testFinalEqn[simp]

val th = SCONV [Excl "AND_CLAUSES"] “a ∧ T ∧ b”

val simped = assert (aconv “a ∧ b”) (rhs $ concl th)

(* Test from GitHub issue #1822: suspend after gen_tac introduces a free
   variable that later needs to be re-generalised by GEN *)
Theorem test_suspend_gen:
  ∀x. x ∧ T ⇒ x ∧ T
Proof
  gen_tac >> strip_tac >> conj_tac
  >- suspend "base"
  >> simp[]
QED

Resume test_suspend_gen[base]:
  first_assum ACCEPT_TAC
QED

Finalise test_suspend_gen
