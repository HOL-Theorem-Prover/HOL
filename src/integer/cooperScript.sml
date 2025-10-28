Theory cooper
Ancestors
  integer int_arith

Theorem elim_le[unlisted] = GSYM INT_NOT_LT;

Theorem move_add[unlisted]:
  !x y z:int. (x + y) + z = (x + z) + y
Proof
  REPEAT GEN_TAC THEN CONV_TAC (AC_CONV (INT_ADD_ASSOC, INT_ADD_COMM))
QED

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

Theorem NOT_AND_IMP[unlisted] =
  tautLib.TAUT_PROVE ``!p q. ~(p /\ q) = (p ==> ~q)``;

Theorem DISJ_NEQ_ELIM[unlisted]:
  !P x v:'a. ~(x = v) \/ P x <=> ~(x = v) \/ P v
Proof
  REWRITE_TAC [GSYM IMP_DISJ_THM] THEN REPEAT GEN_TAC THEN EQ_TAC THEN
  REPEAT STRIP_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC []
QED

Theorem cpEU_THM[unlisted]:
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

Theorem my_INT_MUL_LID[unlisted]:
  (1 * (c * d) = c * d) /\
  (~1 * (c * d) = ~c * d) /\
  (1 * (c * d + x) = c * d + x) /\
  (~1 * (c * d + x) = ~c * d + ~x) /\
  (~~x = x)
Proof
  REWRITE_TAC [INT_MUL_LID, GSYM INT_NEG_MINUS1, INT_NEG_LMUL,
               INT_NEG_ADD, INT_NEGNEG]
QED

Theorem INT_DIVIDES_NEG'[unlisted] =
  CONV_RULE (DEPTH_CONV FORALL_AND_CONV) INT_DIVIDES_NEG;

Theorem INT_NEG_FLIP_LTL[local]:
  !x y. ~x < y <=> ~y < x
Proof
  REPEAT GEN_TAC THEN
  CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV (GSYM INT_NEGNEG)))) THEN
  REWRITE_TAC [INT_LT_NEG]
QED

Theorem INT_NEG_FLIP_LTR[local]:
  !x y. x < ~y <=> y < ~x
Proof
  REPEAT GEN_TAC THEN
  CONV_TAC (RAND_CONV (LAND_CONV (REWR_CONV (GSYM INT_NEGNEG)))) THEN
  REWRITE_TAC [INT_LT_NEG]
QED

Theorem negated_elim_lt_coeffs1[unlisted] =
  (ONCE_REWRITE_RULE [INT_NEG_FLIP_LTR] o
   REWRITE_RULE [GSYM INT_NEG_RMUL] o
   Q.SPECL [`n`, `m`, `~x`])
  elim_lt_coeffs1;

Theorem negated_elim_lt_coeffs2[unlisted] =
  (ONCE_REWRITE_RULE [INT_NEG_FLIP_LTL] o
   REWRITE_RULE [GSYM INT_NEG_RMUL] o
   Q.SPECL [`n`, `m`, `~x`])
  elim_lt_coeffs2;

Theorem elim_eq_coeffs'[unlisted] =
  CONV_RULE (STRIP_QUANT_CONV (RAND_CONV
                               (BINOP_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))))
  elim_eq_coeffs;

Theorem p6_step[unlisted]:
  (?x:int. K (lo < x /\ x <= hi) x /\ P x) <=>
  lo < hi /\ (P hi \/ (?x:int. K (lo < x /\ x <= hi - 1) x /\ P x))
Proof
  REWRITE_TAC [combinTheory.K_THM, LEFT_AND_OVER_OR] THEN
  EQ_TAC THENL [
    CONV_TAC
      (LAND_CONV (ONCE_REWRITE_CONV [restricted_quantification_simp])) THEN
    STRIP_TAC THENL [
      FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC [],
      ASM_REWRITE_TAC [] THEN DISJ2_TAC THEN
      Q.EXISTS_TAC `x` THEN ASM_REWRITE_TAC []
    ],
    STRIP_TAC THENL [
      Q.EXISTS_TAC `hi` THEN ASM_REWRITE_TAC [INT_LE_REFL],
      ONCE_REWRITE_TAC [restricted_quantification_simp] THEN
      Q.EXISTS_TAC `x` THEN  ASM_REWRITE_TAC []
    ]
  ]
QED

Theorem NOT_EXISTS_THM'[unlisted] = GEN_ALL $ SYM $
  PURE_REWRITE_RULE [NOT_CLAUSES] $ BETA_RULE $
  SPEC ``\x:'a. ~ P x : bool`` boolTheory.NOT_EXISTS_THM;

Theorem NOT_NOT[unlisted] = tautLib.TAUT_PROVE ``~~p:bool = p``;

Theorem K_THM'[unlisted] =
  INST_TYPE [(alpha |-> bool), (beta |-> ``:int``)] combinTheory.K_THM;
