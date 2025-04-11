open HolKernel boolLib
open integerTheory int_arithTheory

val _ = new_theory "cooper";

Theorem elim_le = GSYM INT_NOT_LT;

Theorem move_add:
  !x y z:int. (x + y) + z = (x + z) + y
Proof
  REPEAT GEN_TAC THEN CONV_TAC (AC_CONV (INT_ADD_ASSOC, INT_ADD_COMM))
QED

Theorem F_not = List.nth(CONJUNCTS NOT_CLAUSES,2);

val AND_CLAUSES0 = CONJUNCTS (Q.ID_SPEC AND_CLAUSES);
val OR_CLAUSES0 = CONJUNCTS (Q.ID_SPEC OR_CLAUSES);
Theorem T_and_l = GEN_ALL (List.nth(AND_CLAUSES0, 0));
Theorem T_and_r = GEN_ALL (List.nth(AND_CLAUSES0, 1));
Theorem F_and_l = GEN_ALL (List.nth(AND_CLAUSES0, 2));
Theorem F_and_r = GEN_ALL (List.nth(AND_CLAUSES0, 3));
Theorem T_or_l = GEN_ALL (List.nth(OR_CLAUSES0, 0));
Theorem T_or_r = GEN_ALL (List.nth(OR_CLAUSES0, 1));
Theorem F_or_l = GEN_ALL (List.nth(OR_CLAUSES0, 2));
Theorem F_or_r = GEN_ALL (List.nth(OR_CLAUSES0, 3));

Theorem NOT_NOT_P = List.nth(CONJUNCTS NOT_CLAUSES, 0);
Theorem NOT_OR = GEN_ALL (#2 (CONJ_PAIR (SPEC_ALL DE_MORGAN_THM)));
Theorem NOT_AND = GEN_ALL (#1 (CONJ_PAIR (SPEC_ALL DE_MORGAN_THM)));

Theorem NOT_AND_IMP =
  tautLib.TAUT_PROVE ``!p q. ~(p /\ q) = (p ==> ~q)``;

Theorem DISJ_NEQ_ELIM:
  !P x v:'a. ~(x = v) \/ P x <=> ~(x = v) \/ P v
Proof
  REWRITE_TAC [GSYM IMP_DISJ_THM] THEN REPEAT GEN_TAC THEN EQ_TAC THEN
  REPEAT STRIP_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC []
QED

Theorem cpEU_THM:
  !P. (?!x:int. P x) <=>
      (?x. P x) /\ (!y y'. (~P y \/ ~P y') \/ (1*y = 1*y'))
Proof
  REWRITE_TAC [INT_MUL_LID, EXISTS_UNIQUE_THM, GSYM DE_MORGAN_THM,
               GSYM IMP_DISJ_THM]
QED

Theorem simple_disj_congruence:
  !p q r. (~p ==> (q = r)) ==> (p \/ q <=> p \/ r)
Proof
  REPEAT GEN_TAC THEN MAP_EVERY Q.ASM_CASES_TAC [`p`,`q`,`r`] THEN
  ASM_REWRITE_TAC []
QED

Theorem simple_conj_congruence:
  !p q r. (p ==> (q = r)) ==> (p /\ q <=> p /\ r)
Proof
  REPEAT GEN_TAC THEN MAP_EVERY Q.ASM_CASES_TAC [`p`,`q`,`r`] THEN
  ASM_REWRITE_TAC []
QED

val _ = export_theory ();
