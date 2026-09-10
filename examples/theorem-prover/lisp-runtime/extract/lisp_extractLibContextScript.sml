Theory lisp_extractLibContext[bare]
Ancestors
  bool pair combin lisp_semantics
Libs
  HolKernel Parse boolLib bossLib simpLib

(* ------------------------------------------------------------------------- *)
(* Lemmas lisp_extractLib.sml formerly proved as it loaded.  A library is    *)
(* loaded before its client's new_theory, so there was no current theory to  *)
(* prove against; proving them in a theory of their own removes that.        *)
(* ------------------------------------------------------------------------- *)

Theorem eq_imp_imp:
  (x = (y:bool)) ==> (x ==> y)
Proof
  SIMP_TAC std_ss []
QED

Theorem R_ev_EXAPND_LEMMA:
  (b ==> R_ev x y) ==>
  (b ==> R_ev x (FST y,FST (SND y),FST (SND (SND y)),SND (SND (SND y))))
Proof
  SIMP_TAC std_ss []
QED

Theorem let_lemma:
  !f x. f x = LET (f:'a->'b) x
Proof
  SIMP_TAC std_ss [LET_DEF]
QED

Theorem pair_eq_lemma:
  !p x y. ((x,y) = p) <=> (((x:'a) = FST p) /\ ((y:'b) = SND p))
Proof
  Cases_on `p` \\ SIMP_TAC std_ss []
QED
