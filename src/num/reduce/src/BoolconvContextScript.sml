Theory BoolconvContext[bare]
Libs
  HolKernel Parse boolLib

(* ------------------------------------------------------------------------- *)
(* Conjunctions of boolean simplifications Boolconv.sml formerly proved as   *)
(* it loaded.                                                                *)
(* ------------------------------------------------------------------------- *)

Theorem BOOLCONV_NOT:
  (~T <=> F) /\ (~F <=> T) /\ !t. ~~t <=> t
Proof REWRITE_TAC [NOT_CLAUSES]
QED

Theorem BOOLCONV_AND:
  (!t. T /\ t <=> t) /\ (!t. t /\ T <=> t) /\
  (!t. F /\ t <=> F) /\ (!t. t /\ F <=> F) /\ (!t. t /\ t <=> t)
Proof REWRITE_TAC [AND_CLAUSES]
QED

Theorem BOOLCONV_OR:
  (!t. T \/ t <=> T) /\ (!t. t \/ T <=> T) /\
  (!t. F \/ t <=> t) /\ (!t. t \/ F <=> t) /\ (!t. t \/ t <=> t)
Proof REWRITE_TAC [OR_CLAUSES]
QED

Theorem BOOLCONV_IMP:
  (!t. (T ==> t) <=> t) /\ (!t. (t ==> T) <=> T) /\
  (!t. (F ==> t) <=> T) /\ (!t. (t ==> F) <=> ~t) /\
  (!t. (t ==> t) <=> T)
Proof REWRITE_TAC [IMP_CLAUSES]
QED

Theorem BOOLCONV_BEQ:
  (!t. (T <=> t) <=> t) /\ (!t. (t <=> T) <=> t) /\
  (!t. (F <=> t) <=> ~t) /\ (!t. (t <=> F) <=> ~t) /\
  (!t:bool. (t <=> t) <=> T)
Proof REWRITE_TAC [EQ_CLAUSES]
QED

Theorem BOOLCONV_COND:
  (!t1 t2. (if T then t1 else t2) = (t1:'a)) /\
  (!t1 t2. (if F then t1 else t2) = (t2:'a)) /\
  (!b t.   (if b then t else t) = (t:'a))
Proof REWRITE_TAC [COND_CLAUSES, COND_ID]
QED
