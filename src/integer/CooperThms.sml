structure CooperThms :> CooperThms = struct

open HolKernel boolLib
open integerTheory int_arithTheory

(* Fix the grammar used by this file *)
structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars integer_grammars
end
open Parse

val elim_le = GSYM INT_NOT_LT
val elim_gt = int_gt
val elim_ge = int_ge

val move_add = prove(
  ``!x y z:int. (x + y) + z = (x + z) + y``,
  REPEAT GEN_TAC THEN CONV_TAC (AC_CONV (INT_ADD_ASSOC, INT_ADD_COMM)));

val F_not = List.nth(CONJUNCTS NOT_CLAUSES,2)

val AND_CLAUSES0 = CONJUNCTS (Q.ID_SPEC AND_CLAUSES)
val OR_CLAUSES0 = CONJUNCTS (Q.ID_SPEC OR_CLAUSES)
val T_and_l = GEN_ALL (List.nth(AND_CLAUSES0, 0))
val T_and_r = GEN_ALL (List.nth(AND_CLAUSES0, 1))
val F_and_l = GEN_ALL (List.nth(AND_CLAUSES0, 2))
val F_and_r = GEN_ALL (List.nth(AND_CLAUSES0, 3))
val T_or_l = GEN_ALL (List.nth(OR_CLAUSES0, 0))
val T_or_r = GEN_ALL (List.nth(OR_CLAUSES0, 1))
val F_or_l = GEN_ALL (List.nth(OR_CLAUSES0, 2))
val F_or_r = GEN_ALL (List.nth(OR_CLAUSES0, 3))

val NOT_NOT_P = List.nth(CONJUNCTS NOT_CLAUSES, 0)
val NOT_OR = GEN_ALL (#2 (CONJ_PAIR (SPEC_ALL DE_MORGAN_THM)))
val NOT_AND = GEN_ALL (#1 (CONJ_PAIR (SPEC_ALL DE_MORGAN_THM)))

val NOT_AND_IMP =
  tautLib.TAUT_PROVE (Term`!p q. ~(p /\ q) = (p ==> ~q)`)

val DISJ_NEQ_ELIM = prove(
  ``!P x v:'a. ~(x = v) \/ P x = ~(x = v) \/ P v``,
  REWRITE_TAC [GSYM IMP_DISJ_THM] THEN REPEAT GEN_TAC THEN EQ_TAC THEN
  REPEAT STRIP_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC []);


val cpEU_THM = prove(
  ``!P. (?!x:int. P x) =
        (?x. P x) /\ (!y y'. (~P y \/ ~P y') \/ (1*y = 1*y'))``,
  REWRITE_TAC [INT_MUL_LID, EXISTS_UNIQUE_THM, GSYM DE_MORGAN_THM,
               GSYM IMP_DISJ_THM]);

val simple_disj_congruence = prove(
  ``!p q r. (~p ==> (q = r)) ==> (p \/ q = p \/ r)``,
  REPEAT GEN_TAC THEN MAP_EVERY Q.ASM_CASES_TAC [`p`,`q`,`r`] THEN
  ASM_REWRITE_TAC []);

val simple_conj_congruence = prove(
  ``!p q r. (p ==> (q = r)) ==> (p /\ q = p /\ r)``,
  REPEAT GEN_TAC THEN MAP_EVERY Q.ASM_CASES_TAC [`p`,`q`,`r`] THEN
  ASM_REWRITE_TAC []);

end
