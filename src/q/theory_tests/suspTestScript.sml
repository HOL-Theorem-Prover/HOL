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

val _ = set_suspended_goal Manager.id_tacm {
  label_name = "p", suspension_name = "willsplit"}

val psubgoal = resume{label_name = "p", suspension_name = "willsplit"}
  (ASM_REWRITE_TAC[])

val _ = set_suspended_goal Manager.id_tacm {
  label_name = "q", suspension_name = "willsplit"}

val qsubgoal = resume{label_name = "q", suspension_name = "willsplit"}
  (RES_TAC)

val final = finalise_suspended_thm (DB_dtype.mkloc(#(FILE),#(LINE),true))
                                   "willsplit"

val th = fetch "suspTest" "willsplit"
