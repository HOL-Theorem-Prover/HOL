open HolKernel basicHol90Lib Parse
infix THEN THENC THENL |->
infixr -->

open integerTheory intLib Psyntax listTheory

open simpLib boolSimps BasicProvers SingleStep
infix ++
infix 8 by

val _ = new_theory "int_arith";


val int_ss = bool_ss ++ intSimps.INT_REDUCE_ss
val REDUCE_CONV = SIMP_CONV int_ss []

val not_less = store_thm(
  "not_less",
  Term`~(x:int < y) = y < x + 1`,
  EQ_TAC THEN REWRITE_TAC [INT_NOT_LT] THEN STRIP_TAC THENL [
    IMP_RES_TAC INT_LT_ADD1,
    REWRITE_TAC [INT_LE_LT] THEN Q.ASM_CASES_TAC `y = x` THEN
    ASM_REWRITE_TAC [] THEN Q.ASM_CASES_TAC `x < y` THENL [
      IMP_RES_TAC INT_DISCRETE,
      MP_TAC (Q.SPEC `x` (Q.SPEC `y` INT_LT_TOTAL)) THEN
      ASM_REWRITE_TAC []
    ]
  ]);

val elim_eq = store_thm(
  "elim_eq",
  Term`(x:int = y) = (x < y + 1 /\ y < x + 1)`,
  REWRITE_TAC [GSYM not_less] THEN EQ_TAC THEN STRIP_TAC THENL [
    ASM_REWRITE_TAC [INT_LT_REFL],
    MP_TAC (Q.SPECL [`x`,`y`] INT_LT_TOTAL) THEN
    ASM_REWRITE_TAC []
  ]);

val move_all_right = store_thm(
  "move_all_right",
  ``!x y. x < y = 0 < y + ~x``,
  REWRITE_TAC [INT_LT_ADDNEG, INT_ADD_LID]);
val move_all_left = store_thm(
  "move_all_left",
  ``!x y. x < y = x + ~y < 0``,
  REWRITE_TAC [INT_LT_ADDNEG2, INT_ADD_LID]);
val move_left_left = store_thm(
  "move_left_left",
  ``!x y z. x < y + z = x + ~y < z``,
  REPEAT GEN_TAC THEN REWRITE_TAC [INT_LT_ADDNEG2] THEN
  CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV INT_ADD_COMM))) THEN REFL_TAC);
val move_left_right = store_thm(
  "move_left_right",
  ``!x y z. x + y < z = y < z + ~x``,
  REPEAT GEN_TAC THEN REWRITE_TAC [INT_LT_ADDNEG] THEN
  CONV_TAC (LHS_CONV (RATOR_CONV (RAND_CONV (REWR_CONV INT_ADD_COMM)))) THEN
  REFL_TAC);

val lcm_eliminate = store_thm(
  "lcm_eliminate",
  ``!P c. (?x. P (c * x)) = (?x. P x /\ c int_divides x)``,
  REPEAT GEN_TAC THEN SIMP_TAC bool_ss [INT_DIVIDES] THEN
  PROVE_TAC [INT_MUL_SYM]);


val justify_multiplication = store_thm(
  "justify_multiplication",
  --`!n x y:int. 0 < n ==> (x < y = n * x < n * y)`--,
  REPEAT STRIP_TAC THEN
  `n * x < n * y = 0 < n * y - n * x`
     by PROVE_TAC [INT_LT_ADD_SUB, INT_ADD_LID] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC [GSYM INT_SUB_LDISTRIB, INT_MUL_SIGN_CASES] THEN
  `~(n < 0)` by PROVE_TAC [INT_LT_TRANS, INT_LT_REFL] THEN
  ASM_REWRITE_TAC [INT_ADD_LID, GSYM INT_LT_ADD_SUB]);

val justify_divides = store_thm(
  "justify_divides",
  --`!n x y:int. 0 < n ==> (x int_divides y = n * x int_divides n * y)`--,
  REWRITE_TAC [INT_DIVIDES] THEN REPEAT STRIP_TAC THEN EQ_TAC THEN
  STRIP_TAC THENL [
    PROVE_TAC [INT_MUL_ASSOC, INT_MUL_SYM],
    Q.EXISTS_TAC `m` THEN MATCH_MP_TAC INT_EQ_LMUL_IMP THEN
    Q.EXISTS_TAC `n` THEN
    PROVE_TAC [INT_LT_REFL, INT_MUL_ASSOC, INT_MUL_SYM]
  ]);

val INT_SUB_SUB3 = store_thm(
  "INT_SUB_SUB3",
  Term`!x y z:int. x - (y - z) = x + z - y`,
  REWRITE_TAC [int_sub, INT_NEG_ADD, INT_NEGNEG] THEN
  PROVE_TAC [INT_ADD_COMM, INT_ADD_ASSOC]);

(* |- !a b c:int. a - b + c = a + c - b *)
val move_sub = let
  val thm0 = SYM (SPEC_ALL INT_ADD2_SUB2)
  val thm1 = Thm.INST [(mk_var("d", int_ty) |-> zero_tm)] thm0
  val thm2 = REWRITE_RULE [INT_ADD_RID, INT_SUB_RZERO] thm1
in
  save_thm("move_sub", GEN_ALL thm2)
end

val can_get_small = store_thm(
  "can_get_small",
  Term`!x:int y d. 0 < d ==> ?c. 0 < c /\ y - c * d < x`,
  REPEAT STRIP_TAC THEN
  Q.EXISTS_TAC `if y < x then 1
                else if y = x then 1
                else 2 * (y - x)` THEN
  REPEAT COND_CASES_TAC THEN CONV_TAC REDUCE_CONV THENL [
    REWRITE_TAC [INT_MUL_LID] THEN
    MATCH_MP_TAC INT_LT_TRANS THEN Q.EXISTS_TAC `y` THEN
    ASM_REWRITE_TAC [INT_LT_SUB_RADD, INT_LT_ADDR],
    POP_ASSUM SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC [INT_LT_SUB_RADD, INT_LT_ADDR, INT_MUL_LID],
    ASM_SIMP_TAC int_ss [INT_MUL_SIGN_CASES, INT_SUB_LDISTRIB,
                                 INT_SUB_RDISTRIB, INT_SUB_LT,
                                 INT_SUB_SUB3] THEN
    `x < y` by PROVE_TAC [INT_LT_TOTAL] THEN
    ASM_REWRITE_TAC [GSYM move_sub, INT_LT_ADD_SUB] THEN
    `2 * y * d = y * (2 * d)` by PROVE_TAC [INT_MUL_SYM, INT_MUL_ASSOC] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    `2 * x * d = x * (2 * d)` by PROVE_TAC [INT_MUL_SYM, INT_MUL_ASSOC] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    CONV_TAC
     (BINOP_CONV (RATOR_CONV (RAND_CONV (REWR_CONV (GSYM INT_MUL_RID))))) THEN
    REWRITE_TAC [GSYM INT_SUB_LDISTRIB] THEN
    ONCE_REWRITE_TAC [GSYM INT_LT_NEG] THEN
    REWRITE_TAC [INT_NEG_RMUL, INT_NEG_SUB] THEN
    Q.SUBGOAL_THEN `0 < 2 * d - 1`
      (fn th => PROVE_TAC [th, justify_multiplication, INT_MUL_SYM]) THEN
    `?n. d = &n` by PROVE_TAC [NUM_POSINT_EXISTS, INT_LE_LT] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    Cases_on `n` THEN
    FULL_SIMP_TAC bool_ss [INT_LT_REFL, INT, INT_LDISTRIB] THEN
    REWRITE_TAC [int_sub] THEN
    CONV_TAC (REDUCE_CONV THENC RAND_CONV collect_additive_consts) THEN
    REPEAT (POP_ASSUM (K ALL_TAC)) THEN Induct_on `n'` THENL [
      CONV_TAC REDUCE_CONV,
      REWRITE_TAC [INT, INT_LDISTRIB] THEN
      CONV_TAC (REDUCE_CONV THENC RAND_CONV collect_additive_consts) THEN
      MATCH_MP_TAC INT_LT_TRANS THEN Q.EXISTS_TAC `2 * &n' + 1` THEN
      ASM_REWRITE_TAC [INT_LT_LADD] THEN CONV_TAC REDUCE_CONV
    ]
  ]);

val positive_product_implication = store_thm(
  "positive_product_implication",
  Term`!c d:int. 0 < c /\ 0 < d ==> 0 < c * d`,
  SIMP_TAC int_ss [INT_MUL_SIGN_CASES]);

val restricted_quantification_simp = store_thm(
  "restricted_quantification_simp",
  Term`!low high x:int.
           (low < x /\ x <= high) =
           (low < high /\ ((x = high) \/ (low < x /\ x <= high - 1)))`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    `low < high` by PROVE_TAC [INT_LTE_TRANS] THEN
    FULL_SIMP_TAC int_ss [INT_LE_LT] THEN
    `~(x = high)` by PROVE_TAC [INT_LT_REFL] THEN
    POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    `high - 1 < x` by PROVE_TAC [INT_LT_TOTAL] THEN
    `high < x + 1` by PROVE_TAC [INT_LT_SUB_RADD] THEN
    PROVE_TAC [INT_DISCRETE],
    ASM_SIMP_TAC bool_ss [INT_LE_REFL],
    FULL_SIMP_TAC int_ss [INT_LE_LT] THEN
    DISJ1_TAC THENL [
      MATCH_MP_TAC INT_LT_TRANS THEN
      Q.EXISTS_TAC `high - 1`,
      ALL_TAC
    ] THEN
    ASM_REWRITE_TAC [INT_LT_SUB_RADD, INT_LT_ADDR] THEN
    CONV_TAC REDUCE_CONV
  ]);

val top_and_lessers = store_thm(
  "top_and_lessers",
  Term`!P d:int x0. (!x. P x ==> P(x - d)) /\ P x0 ==>
              !c. 0 < c ==> P(x0 - c * d)`,
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC (Q.SPEC `c` INT_NUM_CASES) THENL [
    (* c strictly positive *)
    FIRST_ASSUM SUBST_ALL_TAC THEN
    Induct_on `n` THEN REWRITE_TAC [INT_LT,
                                    prim_recTheory.LESS_0,
                                    numTheory.NOT_SUC, INT,
                                    INT_RDISTRIB, INT_MUL_LID] THEN
    Cases_on `n` THENL [
      PROVE_TAC [INT_MUL_LZERO, INT_ADD_LID],
      FULL_SIMP_TAC bool_ss [INT_INJ, prim_recTheory.INV_SUC_EQ,
                             prim_recTheory.LESS_0, INT_LT,
                             numTheory.NOT_SUC] THEN
      Q.ABBREV_TAC `q = &(SUC n')*d` THEN
      Q.SUBGOAL_THEN `x0 - (q + d) = x0 - q - d` (fn th => PROVE_TAC [th]) THEN
      REWRITE_TAC [INT_SUB_CALCULATE, INT_NEG_ADD] THEN
      CONV_TAC (AC_CONV(INT_ADD_ASSOC, INT_ADD_COMM))
    ],
    (* c strictly negative *)
    FULL_SIMP_TAC bool_ss [INT_NEG_GT0, INT_LT,
                                   prim_recTheory.NOT_LESS_0],
    (* c zero *)
    PROVE_TAC [INT_LT_REFL]
  ]);

val in_additive_range = store_thm(
  "in_additive_range",
  Term`!low d x.
          low < x /\ x <= low + d =
          ?j. (x = low + j) /\ 0 < j /\ j <= d`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    Q.SUBGOAL_THEN `?n. d = &n` (STRIP_THM_THEN SUBST_ALL_TAC) THENL [
      STRIP_ASSUME_TAC (Q.SPEC `d` INT_NUM_CASES) THENL [
        PROVE_TAC [],
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        FULL_SIMP_TAC bool_ss [GSYM int_sub, INT_LE_SUB_LADD] THEN
        `x + &n < x` by PROVE_TAC [INT_LET_TRANS] THEN
        `&n < x - x` by PROVE_TAC [INT_LT_ADD_SUB, INT_ADD_COMM] THEN
        `&n < 0` by PROVE_TAC [INT_SUB_REFL] THEN
        FULL_SIMP_TAC bool_ss [INT_LT, prim_recTheory.NOT_LESS_0],
        PROVE_TAC []
      ],
      Induct_on `n` THENL [
        PROVE_TAC [INT_LTE_TRANS, INT_ADD_RID, INT_LT_REFL],
        REWRITE_TAC [INT_LE_LT, INT] THEN STRIP_TAC THENL [
          `x <= low + &n` by PROVE_TAC [not_less, INT_ADD_ASSOC,
                                        INT_NOT_LT] THEN
          PROVE_TAC [INT_LT_ADD1],
          `0 < &n + 1` by PROVE_TAC [INT, prim_recTheory.LESS_0, INT_LT] THEN
          PROVE_TAC []
        ]
      ]
    ],
    ASM_REWRITE_TAC [INT_LT_ADDR, INT_LE_LADD]
  ]);

val MEM_base = store_thm(
  "MEM_base",
  Term`!e l. MEM e (e::l)`,
  REWRITE_TAC [MEM]);

val MEM_build = store_thm(
  "MEM_build",
  Term`!l1 e1 e2. MEM e1 l1 ==> MEM e1 (e2::l1)`,
  SIMP_TAC bool_ss [MEM]);

val subtract_to_small = store_thm(
  "subtract_to_small",
  Term`!x d:int. 0 < d ==> ?k. 0 < x - k * d /\ x - k * d <= d`,
  REPEAT STRIP_TAC THEN
  Q.SUBGOAL_THEN `ABS (x - x/d * d) < ABS d` ASSUME_TAC THENL [
    `!x y z. (x = y + z) = (x - y = z)`
       by PROVE_TAC [INT_EQ_SUB_LADD, INT_ADD_COMM] THEN
    POP_ASSUM (fn th =>
      `x - x/d*d = x % d` by PROVE_TAC [INT_DIVISION, INT_LT_REFL, th]) THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    PROVE_TAC [INT_LT_REFL, INT_ABS_MOD_LT],
    ALL_TAC
  ] THEN
  POP_ASSUM (fn th =>
    `ABS (x - x/d * d) < d` by PROVE_TAC [th, INT_ABS_EQ_ID, INT_LE_LT]) THEN
  Q.ABBREV_TAC `p = x - x/d * d` THEN
  STRIP_ASSUME_TAC (Q.SPEC `p` INT_LT_NEGTOTAL) THENL [
    Q.EXISTS_TAC `x/d - 1` THEN POP_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC bool_ss [INT_SUB_RDISTRIB, INT_SUB_0, INT_MUL_LID] THEN
    POP_ASSUM (SUBST_ALL_TAC o SYM) THEN
    ASM_SIMP_TAC bool_ss [INT_LE_REFL, INT_SUB_SUB2],
    Q.EXISTS_TAC `x/d` THEN
    `ABS p = p` by PROVE_TAC [INT_ABS_EQ_ID, INT_LE_LT] THEN
    POP_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC bool_ss [INT_LE_LT],
    FULL_SIMP_TAC bool_ss [INT_NEG_GT0] THEN
    Q.EXISTS_TAC `x/d - 1` THEN
    SIMP_TAC bool_ss [INT_SUB_RDISTRIB, INT_MUL_LID] THEN
    `!x y z:int. x - (y - z) = x - y + z`
       by PROVE_TAC [move_sub, INT_SUB_SUB3] THEN
    POP_ASSUM (fn th => ASM_REWRITE_TAC [th]) THEN CONJ_TAC THENL [
      STRIP_ASSUME_TAC (Q.SPEC `p` INT_NUM_CASES) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FULL_SIMP_TAC bool_ss [INT_LT, prim_recTheory.NOT_LESS_0] THEN
      ONCE_REWRITE_TAC [INT_ADD_COMM] THEN
      FULL_SIMP_TAC bool_ss [GSYM move_all_right, INT_ABS_NEG, INT_ABS_NUM],
      REWRITE_TAC [GSYM INT_NOT_LT] THEN
      ONCE_REWRITE_TAC [INT_ADD_COMM] THEN
      REWRITE_TAC [INT_LT_ADDR] THEN ASM_REWRITE_TAC [INT_NOT_LT, INT_LE_LT]
    ]
  ]);


open arithmeticTheory
val INT_LT_ADD_NUMERAL = store_thm(
  "INT_LT_ADD_NUMERAL",
  Term`!x:int y. x < x + &(NUMERAL (NUMERAL_BIT1 y)) /\
                 x < x + &(NUMERAL (NUMERAL_BIT2 y)) /\
                 ~(x < x + ~(&(NUMERAL y)))`,
  SIMP_TAC bool_ss [INT_LT_ADDR, INT_LT, NUMERAL_DEF, NUMERAL_BIT1,
                    NUMERAL_BIT2, ADD_CLAUSES, prim_recTheory.LESS_0,
                    INT_NEG_GT0, prim_recTheory.NOT_LESS_0]);


val INT_NUM_FORALL = store_thm(
  "INT_NUM_FORALL",
  Term`(!n:num. P (&n)) = (!x:int. 0 <= x ==> P x)`,
  EQ_TAC THEN REPEAT STRIP_TAC THENL [
    PROVE_TAC [NUM_POSINT_EXISTS],
    POP_ASSUM MATCH_MP_TAC THEN SIMP_TAC bool_ss [INT_LE, ZERO_LESS_EQ]
  ]);

val INT_NUM_EXISTS = store_thm(
  "INT_NUM_EXISTS",
  Term`(?n:num. P(&n)) = (?x:int. 0 <= x /\ P x)`,
  EQ_TAC THEN REPEAT STRIP_TAC THENL [
    PROVE_TAC [INT_LE, ZERO_LESS_EQ],
    PROVE_TAC [NUM_POSINT_EXISTS]
  ]);

val INT_NUM_UEXISTS = store_thm(
  "INT_NUM_UEXISTS",
  Term`(?!n:num. P (&n)) = (?!x:int. 0 <= x /\ P x)`,
  EQ_TAC THEN SIMP_TAC bool_ss [EXISTS_UNIQUE_THM] THEN
  REPEAT STRIP_TAC THENL [
    PROVE_TAC [INT_LE, ZERO_LESS_EQ],
    PROVE_TAC [INT_INJ, NUM_POSINT_EXISTS],
    PROVE_TAC [NUM_POSINT_EXISTS],
    PROVE_TAC [INT_INJ, ZERO_LESS_EQ, INT_LE]
  ]);

val INT_NUM_SUB = store_thm(
  "INT_NUM_SUB",
  Term`!n m:num. &(n - m) = if int_of_num n < &m then 0i else &n - &m`,
  SIMP_TAC (bool_ss ++ COND_elim_ss) [INT_LT, INT_INJ] THEN
  REPEAT GEN_TAC THEN Q.ASM_CASES_TAC `n < m` THEN
  ASM_SIMP_TAC bool_ss [SUB_EQ_0, LESS_OR_EQ] THEN
  PROVE_TAC [INT_SUB, NOT_LESS]);

val _ = export_theory();
