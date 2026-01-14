Theory suspTest[bare]

(* tests suspension and resumption without any "modern syntax" for steps
   after the first
*)

Libs HolKernel Parse boolLib markerLib Q

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

val _ = set_suspended_goal Manager.id_tacm {
  label_name = "p", suspension_name = "willsplit"}

val psubgoal = resume{label_name = "p", suspension_name = "willsplit"}
  (ASM_REWRITE_TAC[])

val _ = set_suspended_goal Manager.id_tacm {
  label_name = "q", suspension_name = "willsplit"}

val qsubgoal = resume{label_name = "q", suspension_name = "willsplit"}
  (RES_TAC)

val q2sg = resume{label_name = "q", suspension_name = "willsplit2"}
  (SUFF_TAC “F” THENL [REWRITE_TAC[], suspend "q"])

val _ = set_suspended_goal Manager.id_tacm {
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
