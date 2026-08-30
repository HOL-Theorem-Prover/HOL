Theory ppc_LibContext[bare]
Ancestors
  words ppc_seq_monad
Libs
  HolKernel Parse boolLib bossLib wordsLib simpLib

(* ------------------------------------------------------------------------- *)
(* Lemmas ppc_Lib.sml formerly proved as it loaded.  A library is loaded      *)
(* before its client's new_theory, so there was no current theory to prove    *)
(* against; proving them in a theory of their own removes that.               *)
(* ------------------------------------------------------------------------- *)

Theorem address_lemma:
  ~(0w = 1w:word32) /\ ~(0w = 2w:word32) /\ ~(0w = 3w:word32) /\
  ~(1w = 2w:word32) /\ ~(1w = 3w:word32) /\ ~(2w = 3w:word32)
Proof
  EVAL_TAC
QED

Theorem if_SOME:
  (if b then SOME((),x:ppc_state) else SOME((),y)) = SOME ((),if b then x else y)
Proof
  Cases_on `b` THEN SIMP_TAC std_ss []
QED
