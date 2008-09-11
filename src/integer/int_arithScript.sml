structure int_arithScript = struct

open HolKernel boolLib Parse

open integerTheory intSyntax dividesTheory

open simpLib boolSimps BasicProvers SingleStep

val arith_ss = bool_ss ++ numSimps.old_ARITH_ss

val _ = new_theory "int_arith";


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

val less_to_leq_samel = store_thm(
  "less_to_leq_samel",
  Term`!x y. x < y = x <= y + ~1`,
  REWRITE_TAC [int_le, not_less, GSYM INT_ADD_ASSOC, INT_ADD_LINV,
               INT_ADD_RID]);
val less_to_leq_samer = store_thm(
  "less_to_leq_samer",
  Term`!x y:int. x < y = x + 1 <= y`,
  REWRITE_TAC [int_le, not_less, INT_LT_RADD]);

val lt_move_all_right = store_thm(
  "lt_move_all_right",
  ``!x y. x < y = 0 < y + ~x``,
  REWRITE_TAC [INT_LT_ADDNEG, INT_ADD_LID]);
val lt_move_all_left = store_thm(
  "lt_move_all_left",
  ``!x y. x < y = x + ~y < 0``,
  REWRITE_TAC [INT_LT_ADDNEG2, INT_ADD_LID]);
val lt_move_left_left = store_thm(
  "lt_move_left_left",
  ``!x y z. x < y + z = x + ~y < z``,
  REPEAT GEN_TAC THEN REWRITE_TAC [INT_LT_ADDNEG2] THEN
  CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV INT_ADD_COMM))) THEN REFL_TAC);
val lt_move_left_right = store_thm(
  "lt_move_left_right",
  ``!x y z. x + y < z = y < z + ~x``,
  REPEAT GEN_TAC THEN REWRITE_TAC [INT_LT_ADDNEG] THEN
  CONV_TAC (LHS_CONV (RATOR_CONV (RAND_CONV (REWR_CONV INT_ADD_COMM)))) THEN
  REFL_TAC);

val le_move_right_left = store_thm(
  "le_move_right_left",
  ``!x y z. x <= y + z = x + ~z <= y``,
  REWRITE_TAC [INT_LE_SUB_RADD, GSYM int_sub]);

val le_move_all_right = store_thm(
  "le_move_all_right",
  ``!x y. x <= y = 0 <= y + ~x``,
  REWRITE_TAC [GSYM int_sub, INT_LE_SUB_LADD, INT_ADD_LID]);


val eq_move_all_right = store_thm(
  "eq_move_all_right",
  ``!x y. (x = y) = (0 = y + ~x)``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    SIMP_TAC bool_ss [INT_ADD_RINV],
    SIMP_TAC bool_ss [GSYM int_sub, INT_EQ_SUB_LADD, INT_ADD_LID]
  ]);
val eq_move_all_left = store_thm(
  "eq_move_all_left",
  ``!x y. (x = y) = (x + ~y = 0)``,
  PROVE_TAC [INT_ADD_COMM, eq_move_all_right]);
val eq_move_left_left = store_thm(
  "eq_move_left_left",
  ``!x y z. (x = y + z) = (x + ~y = z)``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC [INT_ADD_COMM] THEN
    REWRITE_TAC [INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID],
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    ONCE_REWRITE_TAC [INT_ADD_COMM] THEN
    REWRITE_TAC [GSYM INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_RID]
  ]);
val eq_move_left_right = store_thm(
  "eq_move_left_right",
  ``!x y z. (x + y = z) = (y = z + ~x)``,
  PROVE_TAC [INT_ADD_COMM, eq_move_left_left]);

val eq_move_right_left = store_thm(
  "eq_move_right_left",
  ``!x y z. (x = y + z) = (x + ~z = y)``,
  PROVE_TAC [INT_ADD_COMM, eq_move_left_left]);

val lcm_eliminate = store_thm(
  "lcm_eliminate",
  ``!P c. (?x. P (c * x)) = (?x. P x /\ c int_divides x)``,
  REPEAT GEN_TAC THEN SIMP_TAC bool_ss [INT_DIVIDES] THEN
  PROVE_TAC [INT_MUL_SYM]);


val lt_justify_multiplication = store_thm(
  "lt_justify_multiplication",
  --`!n x y:int. 0 < n ==> (x < y = n * x < n * y)`--,
  REPEAT STRIP_TAC THEN
  `n * x < n * y = 0 < n * y - n * x`
     by PROVE_TAC [INT_LT_ADD_SUB, INT_ADD_LID] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC [GSYM INT_SUB_LDISTRIB, INT_MUL_SIGN_CASES] THEN
  `~(n < 0)` by PROVE_TAC [INT_LT_TRANS, INT_LT_REFL] THEN
  ASM_REWRITE_TAC [INT_ADD_LID, GSYM INT_LT_ADD_SUB]);

val eq_justify_multiplication = store_thm(
  "eq_justify_multiplication",
  --`!n x y:int. 0 < n ==> ((x = y) = (n * x = n * y))`--,
  PROVE_TAC [INT_EQ_RMUL, INT_LT_REFL, INT_MUL_COMM]);

val justify_divides = store_thm(
  "justify_divides",
  --`!n x y:int. 0 < n ==> (x int_divides y = n * x int_divides n * y)`--,
  PROVE_TAC [INT_DIVIDES_MUL_BOTH, INT_LT_REFL]);

val justify_divides2 = store_thm(
  "justify_divides2",
  --`!n c x y:int.
        n * x int_divides n * y + c =
        n * x int_divides n * y + c /\ n int_divides c`--,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC [] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC [INT_DIVIDES] THEN
  DISCH_THEN (STRIP_THM_THEN
              (SUBST_ALL_TAC o SYM o
               REWRITE_RULE [eq_move_left_left,
                             INT_NEG_RMUL])) THEN
  `m * (n * x) = n * (m * x)` by PROVE_TAC [INT_MUL_COMM, INT_MUL_ASSOC] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC [GSYM INT_LDISTRIB] THEN
  PROVE_TAC [INT_MUL_COMM]);

val justify_divides3 = store_thm(
  "justify_divides3",
  ``!n x c. n int_divides n * x + c = n int_divides c``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_DIVIDES_LADD THEN
  MATCH_MP_TAC INT_DIVIDES_LMUL THEN MATCH_ACCEPT_TAC INT_DIVIDES_REFL);


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
  SRW_TAC [][] THENL [
    SRW_TAC [][INT_MUL_SIGN_CASES, INT_SUB_LT] THEN PROVE_TAC [INT_LT_TOTAL],
    MATCH_MP_TAC INT_LT_TRANS THEN Q.EXISTS_TAC `y` THEN
    ASM_REWRITE_TAC [INT_LT_SUB_RADD, INT_LT_ADDR],
    ASM_REWRITE_TAC [INT_LT_SUB_RADD, INT_LT_ADDR],
    ASM_SIMP_TAC (srw_ss()) [INT_MUL_SIGN_CASES, INT_SUB_LDISTRIB,
                             INT_SUB_RDISTRIB, INT_SUB_LT, INT_SUB_SUB3] THEN
    `x < y` by PROVE_TAC [INT_LT_TOTAL] THEN
    ASM_REWRITE_TAC [GSYM move_sub, INT_LT_ADD_SUB] THEN
    `2 * y * d = y * (2 * d)` by PROVE_TAC [INT_MUL_SYM, INT_MUL_ASSOC] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    `2 * x * d = x * (2 * d)` by PROVE_TAC [INT_MUL_SYM, INT_MUL_ASSOC] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    CONV_TAC
     (BINOP_CONV (LAND_CONV (REWR_CONV (GSYM INT_MUL_RID)))) THEN
    REWRITE_TAC [GSYM INT_SUB_LDISTRIB] THEN
    ONCE_REWRITE_TAC [GSYM INT_LT_NEG] THEN
    REWRITE_TAC [INT_NEG_RMUL, INT_NEG_SUB] THEN
    Q.SUBGOAL_THEN `0 < 2 * d - 1`
      (fn th => PROVE_TAC [th, lt_justify_multiplication, INT_MUL_SYM]) THEN
    `?n. d = &n` by PROVE_TAC [NUM_POSINT_EXISTS, INT_LE_LT] THEN
    SRW_TAC [][INT_SUB_LT, INT_LT, INT_MUL] THEN
    FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) []
  ]);

val can_get_big = store_thm(
  "can_get_big",
  ``!x:int y d. 0 < d ==> ?c. 0 < c /\ x < y + c * d``,
  REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM INT_LT_SUB_RADD] THEN
  PROVE_TAC [can_get_small]);

val positive_product_implication = store_thm(
  "positive_product_implication",
  Term`!c d:int. 0 < c /\ 0 < d ==> 0 < c * d`,
  SRW_TAC [] [INT_MUL_SIGN_CASES]);

val restricted_quantification_simp = store_thm(
  "restricted_quantification_simp",
  Term`!low high x:int.
           (low < x /\ x <= high) =
           (low < high /\ ((x = high) \/ (low < x /\ x <= high - 1)))`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    `low < high` by PROVE_TAC [INT_LTE_TRANS] THEN
    FULL_SIMP_TAC (srw_ss()) [INT_LE_LT] THEN
    `~(x = high)` by PROVE_TAC [INT_LT_REFL] THEN
    POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    `high - 1 < x` by PROVE_TAC [INT_LT_TOTAL] THEN
    `high < x + 1` by PROVE_TAC [INT_LT_SUB_RADD] THEN
    PROVE_TAC [INT_DISCRETE],
    SRW_TAC [][],
    FULL_SIMP_TAC (srw_ss()) [INT_LE_LT] THEN DISJ1_TAC THENL [
      MATCH_MP_TAC INT_LT_TRANS THEN
      Q.EXISTS_TAC `high - 1`,
      ALL_TAC
    ] THEN
    SRW_TAC [] [INT_LT_SUB_RADD, INT_LT_ADDR]
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

val bot_and_greaters = store_thm(
  "bot_and_greaters",
  Term`!P d:int x0. (!x. P x ==> P (x + d)) /\ P x0 ==>
                    !c. 0 < c ==> P(x0 + c * d)`,
  REPEAT STRIP_TAC THEN
  Q.SPECL_THEN [`P`, `~d`, `x0`] MP_TAC top_and_lessers THEN
  ASM_SIMP_TAC bool_ss [int_sub, INT_NEGNEG, GSYM INT_NEG_RMUL]);

val in_additive_range = store_thm(
  "in_additive_range",
  Term`!low d x:int.
          low < x /\ x <= low + d =
          ?j. (x = low + j) /\ 0 < j /\ j <= d`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    Q.EXISTS_TAC `x - low` THEN
    FULL_SIMP_TAC bool_ss [INT_LE_SUB_RADD, INT_LT_SUB_LADD,
                           INT_ADD_COMM, INT_ADD_LID, INT_SUB_ADD2],
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC bool_ss [INT_LT_SUB_RADD, INT_LT_ADDR, INT_LE_LADD]
  ]);

val in_subtractive_range = store_thm(
  "in_subtractive_range",
  Term`!high d x:int.
          high - d <= x /\ x < high =
          ?j. (x = high - j) /\ 0 < j /\ j <= d`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    Q.EXISTS_TAC `high - x` THEN
    FULL_SIMP_TAC bool_ss [INT_SUB_SUB2, INT_LT_SUB_LADD,
                           INT_ADD_LID, INT_LE_SUB_RADD,
                           INT_ADD_COMM],
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC bool_ss [INT_LT_SUB_RADD, INT_LT_ADDR] THEN
    ASM_SIMP_TAC bool_ss [int_sub, INT_LE_LADD, INT_LE_NEG]
  ]);

val subtract_to_small = store_thm(
  "subtract_to_small",
  Term`!x d:int. 0 < d ==> ?k. 0 < x - k * d /\ x - k * d <= d`,
  REPEAT STRIP_TAC THEN
  `~(d = 0)` by PROVE_TAC [INT_LT_REFL] THEN
  `~(d < 0)` by PROVE_TAC [INT_NOT_LT, INT_LE_LT] THEN
  `(x = x / d * d + x % d) /\ 0 <= x % d /\ x % d < d`
     by PROVE_TAC [INT_DIVISION] THEN
  Q.ABBREV_TAC `q = x / d` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `r = x % d` THEN POP_ASSUM (K ALL_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [INT_LE_LT] THENL [
    Q.EXISTS_TAC `q`,
    Q.EXISTS_TAC `q - 1`
  ] THEN
  SRW_TAC [] [INT_LT_SUB_LADD, INT_LE_SUB_RADD, INT_SUB_RDISTRIB,
              INT_LT_SUB_RADD] THEN
  PROVE_TAC [INT_ADD_COMM, INT_LT_LADD]);

val add_to_great = store_thm(
  "add_to_great",
  Term`!x d:int. 0 < d ==> ?k. 0 < x + k * d /\ x + k * d <= d`,
  REPEAT STRIP_TAC THEN
  Q.SPECL_THEN [`x`, `d`] MP_TAC subtract_to_small THEN
  ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
  Q.EXISTS_TAC `~k` THEN
  ASM_REWRITE_TAC [GSYM INT_NEG_LMUL, GSYM int_sub]);


open arithmeticTheory
val INT_LT_ADD_NUMERAL = store_thm(
  "INT_LT_ADD_NUMERAL",
  Term`!x:int y. x < x + &(NUMERAL (BIT1 y)) /\
                 x < x + &(NUMERAL (BIT2 y)) /\
                 ~(x < x + ~(&(NUMERAL y)))`,
  SIMP_TAC bool_ss [INT_LT_ADDR, INT_LT, NUMERAL_DEF, BIT1,BIT2,
                    ADD_CLAUSES, prim_recTheory.LESS_0,
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

val INT_NUM_COND = store_thm(
  "INT_NUM_COND",
  Term`!b n m. int_of_num (if b then n else m) =
               if b then &n else &m`,
  SIMP_TAC (bool_ss ++ COND_elim_ss) [] THEN PROVE_TAC []);

val INT_NUM_ODD = store_thm(
  "INT_NUM_ODD",
  Term`!n:num. ODD n = ~(2 int_divides &n)`,
  SIMP_TAC bool_ss [ODD_EVEN, EVEN_EXISTS, INT_DIVIDES, GSYM INT_INJ,
                    GSYM INT_MUL] THEN GEN_TAC THEN EQ_TAC THEN
  REPEAT STRIP_TAC THENL [
    Cases_on `&n = 0` THENL [
      POP_ASSUM SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [INT_MUL],
      `0 < &n` by PROVE_TAC [INT_LE_LT, INT_POS] THEN
      `0 < 2i` by SRW_TAC [][] THEN
      `0 < m` by PROVE_TAC [INT_MUL_SIGN_CASES, INT_LT_ANTISYM] THEN
      `?k. m = &k` by PROVE_TAC [NUM_POSINT_EXISTS, INT_LE_LT] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      FIRST_X_ASSUM (MP_TAC o ONCE_REWRITE_RULE [INT_MUL_COMM] o
                     Q.SPEC `k`) THEN
      ASM_REWRITE_TAC []
    ],
    FIRST_X_ASSUM (MP_TAC o Q.SPEC `int_of_num m`) THEN
    ASM_REWRITE_TAC [] THEN MATCH_ACCEPT_TAC INT_MUL_COMM
  ]);

val INT_NUM_EVEN = store_thm(
  "INT_NUM_EVEN",
  Term`!n:num. EVEN n = 2 int_divides &n`,
  SIMP_TAC bool_ss [EVEN_ODD, INT_NUM_ODD]);

val HO_SUB_ELIM = store_thm(
  "HO_SUB_ELIM",
  Term`!(P:int -> bool) a b.
           P(&(a - b)) =
            (int_of_num b <= &a /\ P(&a + ~&b)) \/
            (int_of_num a < &b /\ P 0i)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  FULL_SIMP_TAC (bool_ss ++ COND_elim_ss) [INT_NUM_SUB, LEFT_AND_OVER_OR,
                                           RIGHT_AND_OVER_OR, INT_NOT_LT,
                                           int_sub] THEN
  PROVE_TAC [INT_LE_LT, INT_LT_TOTAL, INT_LET_TRANS, INT_LT_REFL])

val CONJ_EQ_ELIM = store_thm(
  "CONJ_EQ_ELIM",
  Term`!P v e. (v = e) /\ P v = (v = e) /\ P e`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [],
    ASM_REWRITE_TAC []
  ]);

val elim_neg_ones = store_thm(
  "elim_neg_ones",
  Term`!x. x + ~1 + 1 = x`,
  REWRITE_TAC [GSYM INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_RID]);

val elim_minus_ones = store_thm(
  "elim_minus_ones",
  Term`!x:int. (x + 1) - 1 = x`,
  REWRITE_TAC [int_sub, GSYM INT_ADD_ASSOC, INT_ADD_RINV, INT_ADD_RID]);

open gcdTheory

val INT_NUM_DIVIDES = store_thm(
  "INT_NUM_DIVIDES",
  ``!n m. &n int_divides &m = divides n m``,
  SIMP_TAC bool_ss [INT_DIVIDES, dividesTheory.divides_def, EQ_IMP_THM,
                    FORALL_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
  REPEAT STRIP_TAC THENL [
    STRIP_ASSUME_TAC (Q.SPEC `m'` INT_NUM_CASES) THEN
    FULL_SIMP_TAC bool_ss [INT_MUL_CALCULATE, INT_INJ, INT_EQ_CALCULATE,
                           MULT_CLAUSES] THENL [
      PROVE_TAC [],
      PROVE_TAC [MULT_CLAUSES],
      PROVE_TAC [MULT_CLAUSES]
    ],
    Q.EXISTS_TAC `&q` THEN SIMP_TAC bool_ss [INT_MUL]
  ]);

val INT_LINEAR_GCD = store_thm(
  "INT_LINEAR_GCD",
  ``!n m. ?p:int q. p * &n + q * &m = &(gcd n m)``,
  REPEAT GEN_TAC THEN
  Cases_on `n = 0` THENL [
    POP_ASSUM SUBST1_TAC THEN
    SIMP_TAC bool_ss [INT_MUL_RZERO, GCD_0L, INT_ADD_LID] THEN
    PROVE_TAC [INT_MUL_LID],
    ALL_TAC
  ] THEN Cases_on `m = 0` THENL [
    POP_ASSUM SUBST1_TAC THEN
    SIMP_TAC bool_ss [INT_MUL_RZERO, GCD_0R, INT_ADD_RID] THEN
    PROVE_TAC [INT_MUL_LID],
    ALL_TAC
  ] THEN
  `?i j. i * n = j * m + gcd m n` by PROVE_TAC [LINEAR_GCD] THEN
  MAP_EVERY Q.EXISTS_TAC [`&i`, `~&j`] THEN
  ASM_SIMP_TAC bool_ss [INT_MUL_CALCULATE, GSYM eq_move_left_left,
                        GCD_SYM, INT_ADD]);

val INT_DIVIDES_LRMUL = store_thm(
  "INT_DIVIDES_LRMUL",
  ``!p q r. ~(q = 0) ==> ((p * q) int_divides (r * q) = p int_divides r)``,
  REPEAT GEN_TAC THEN SIMP_TAC bool_ss [INT_DIVIDES] THEN
  STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    `(m * p) * q = r * q` by PROVE_TAC [INT_MUL_ASSOC] THEN
    PROVE_TAC [INT_EQ_RMUL],
    PROVE_TAC [INT_MUL_ASSOC]
  ]);


val INT_DIVIDES_RELPRIME_MUL = store_thm(
  "INT_DIVIDES_RELPRIME_MUL",
  ``!p q r.
      (gcd p q = 1) ==>
      (&p int_divides &q * r = &p int_divides r)``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    STRIP_ASSUME_TAC (Q.SPEC `r` INT_NUM_CASES) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC bool_ss [INT_NUM_DIVIDES, INT_MUL_CALCULATE,
                           INT_DIVIDES_NEG] THEN
    PROVE_TAC [L_EUCLIDES, GCD_SYM],
    PROVE_TAC [INT_DIVIDES_RMUL]
  ]);

val INT_MUL_DIV' = prove(
  ``!p q k.
       ~(q = 0) /\ q int_divides p ==> (k * (p / q) = k * p / q)``,
  REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC bool_ss [INT_DIVIDES_MOD0] THEN FULL_SIMP_TAC bool_ss [] THEN
  PROVE_TAC [INT_MUL_DIV]);

val fractions = prove(
  ``!p q r.
       ~(r = 0) /\ r int_divides p /\ r int_divides q ==>
       (p / r + q / r = (p + q) / r)``,
  REPEAT STRIP_TAC THEN
  `?i. p = i * r` by PROVE_TAC [INT_DIVIDES] THEN POP_ASSUM SUBST1_TAC THEN
  `?j. q = j * r` by PROVE_TAC [INT_DIVIDES] THEN POP_ASSUM SUBST1_TAC THEN
  `i * r + j * r = (i + j) * r` by REWRITE_TAC [INT_RDISTRIB] THEN
  POP_ASSUM SUBST1_TAC THEN
  ASM_SIMP_TAC bool_ss [INT_MUL_DIV, INT_MOD_ID, INT_DIV_ID, INT_MUL_RID]);

val gcdthm2 = store_thm(
  "gcdthm2",
  ``!m:num a:num x b d p q.
       (d = gcd a m) /\ (&d = p * &a + q * &m) /\ ~(d = 0) /\
       ~(m = 0) /\ ~(a = 0) ==>
       (&m int_divides (&a * x) + b =
        &d int_divides b /\
        ?t. x = ~p * (b / &d) + t * (&m / &d))``,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [
    STRIP_TAC THEN
    `&d int_divides &a /\ &d int_divides &m` by
       PROVE_TAC [INT_NUM_DIVIDES, GCD_IS_GCD, is_gcd_def] THEN
    `&d int_divides &a * x + b` by PROVE_TAC [INT_DIVIDES_TRANS] THEN
    `&d int_divides &a * x` by PROVE_TAC [INT_DIVIDES_LMUL] THEN
    `&d int_divides b` by PROVE_TAC [INT_DIVIDES_LADD] THEN CONJ_TAC THENL [
      ASM_REWRITE_TAC [],
      ALL_TAC
    ] THEN  (* existential goal remains *)
    Cases_on `d = 1` THENL [
      POP_ASSUM SUBST_ALL_TAC THEN SIMP_TAC bool_ss [INT_DIV_1],
      `?b'. b = b' * &d` by PROVE_TAC [INT_DIVIDES] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o assert (is_eq o concl))) THEN
      REPEAT (DISCH_THEN (ASSUME_TAC o SYM)) THEN
      ASM_SIMP_TAC bool_ss [INT_MUL_DIV, INT_MOD_ID, INT_INJ, INT_DIV_ID,
                            INT_MUL_RID] THEN
      MP_TAC (Q.SPECL [`m`, `a`] FACTOR_OUT_GCD) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (Q.X_CHOOSE_THEN `m'`
                  (Q.X_CHOOSE_THEN `a'` STRIP_ASSUME_TAC)) THEN
      `gcd m a = d` by PROVE_TAC [GCD_SYM] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      POP_ASSUM MP_TAC THEN
      NTAC 2 (POP_ASSUM SUBST_ALL_TAC) THEN
      FULL_SIMP_TAC bool_ss [MULT_EQ_0] THEN
      ASM_SIMP_TAC bool_ss [INT_MUL_DIV, GSYM INT_MUL, INT_MOD_ID, INT_INJ,
                            INT_DIV_ID, INT_MUL_RID] THEN
      FULL_SIMP_TAC bool_ss [GSYM INT_MUL] THEN
      `&m' int_divides &a' * x + b'` by
          (`&a' * &d * x = &a' * x * &d` by
              CONV_TAC(AC_CONV(INT_MUL_ASSOC, INT_MUL_COMM)) THEN
           POP_ASSUM SUBST_ALL_TAC THEN
           `&m' * &d int_divides (&a' * x + b') * &d` by
              ASM_SIMP_TAC bool_ss [INT_RDISTRIB] THEN
           POP_ASSUM MP_TAC THEN
           ASM_SIMP_TAC bool_ss [INT_DIVIDES_LRMUL, INT_INJ]) THEN
      NTAC 2 (POP_ASSUM MP_TAC) THEN POP_ASSUM (K ALL_TAC) THEN
      REPEAT (Q.PAT_ASSUM `y int_divides z` (K ALL_TAC)) THEN
      Q.PAT_ASSUM `T` (K ALL_TAC) THEN
      REWRITE_TAC [INT_MUL_ASSOC, GSYM INT_RDISTRIB] THEN
      CONV_TAC (LAND_CONV (RHS_CONV (REWR_CONV (GSYM INT_MUL_LID)))) THEN
      ASM_SIMP_TAC bool_ss [INT_INJ, INT_EQ_RMUL] THEN
      REPEAT (DISCH_THEN (ASSUME_TAC o GSYM)) THEN
      Q.ABBREV_TAC `b = b'` THEN POP_ASSUM (K ALL_TAC) THEN
      Q.ABBREV_TAC `m = m'` THEN POP_ASSUM (K ALL_TAC) THEN
      Q.ABBREV_TAC `a = a'` THEN POP_ASSUM (K ALL_TAC) THEN
      POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [GCD_SYM])
    ] THEN

    `b * 1 = b * (p * &a + q * &m)` by (AP_TERM_TAC THEN
                                        ASM_REWRITE_TAC []) THEN
    POP_ASSUM (fn th =>
      `b = b * (p * &a) + b * (q * &m)` by
          PROVE_TAC [th, INT_LDISTRIB, INT_MUL_RID]) THEN
    POP_ASSUM (fn th =>
      `b + ~(b * (q * &m)) = b * (p * &a)` by
          MP_TAC th THEN
          SIMP_TAC bool_ss [GSYM eq_move_left_left] THEN
          SIMP_TAC bool_ss [INT_ADD_COMM]) THEN
    POP_ASSUM (fn th =>
      `&a * (b * p) = b + ~(b * (q * &m))` by
         (REWRITE_TAC [th] THEN
          CONV_TAC (AC_CONV(INT_MUL_ASSOC, INT_MUL_COMM)))) THEN
    POP_ASSUM (fn th =>
      `&m int_divides &a * (x + b * p)` by
         (SIMP_TAC bool_ss [INT_LDISTRIB, th] THEN
          REWRITE_TAC [INT_ADD_ASSOC] THEN
          ASM_SIMP_TAC bool_ss [INT_DIVIDES_LADD] THEN
          SIMP_TAC bool_ss [INT_NEG_LMUL, INT_DIVIDES_RMUL,
                            INT_DIVIDES_REFL])) THEN
    `&m int_divides x + b*p`
       by PROVE_TAC [GCD_SYM, INT_DIVIDES_RELPRIME_MUL] THEN
    `?j. j * &m = x + p * b` by PROVE_TAC [INT_DIVIDES, INT_MUL_COMM] THEN
    `x = j * &m + ~(p * b)` by PROVE_TAC [eq_move_left_left, INT_ADD_COMM] THEN
    PROVE_TAC [INT_MUL_CALCULATE, INT_ADD_COMM],

    STRIP_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o assert (is_eq o concl))) THEN
    REPEAT (DISCH_THEN (ASSUME_TAC o SYM)) THEN
    `&d int_divides &m /\ &d int_divides &a` by
       PROVE_TAC [INT_NUM_DIVIDES, GCD_IS_GCD, is_gcd_def] THEN
    REWRITE_TAC [INT_LDISTRIB] THEN
    `&a * (~p * (b / &d)) = b * (~p * &a / &d)` by
       (ASM_SIMP_TAC bool_ss [INT_MUL_DIV', INT_DIVIDES_LMUL,
                              INT_DIVIDES_RMUL, INT_INJ] THEN
        REPEAT (AP_THM_TAC ORELSE AP_TERM_TAC) THEN
        CONV_TAC (AC_CONV(INT_MUL_ASSOC, INT_MUL_COMM))) THEN
    POP_ASSUM SUBST1_TAC THEN
    `&a * (t * (&m / &d)) = &m * (t * &a / &d)` by
       (ASM_SIMP_TAC bool_ss [INT_MUL_DIV', INT_DIVIDES_LMUL,
                              INT_DIVIDES_RMUL, INT_INJ] THEN
        REPEAT (AP_THM_TAC ORELSE AP_TERM_TAC) THEN
        CONV_TAC (AC_CONV(INT_MUL_ASSOC, INT_MUL_COMM))) THEN
    POP_ASSUM SUBST1_TAC THEN
    `b * (~p * &a / &d) + &m * (t * &a / &d) + b =
     &m * (t * &a / &d) + b * (1 + ~p * &a / &d)` by
        (REWRITE_TAC [INT_LDISTRIB, INT_MUL_RID] THEN
         CONV_TAC (AC_CONV(INT_ADD_ASSOC, INT_ADD_COMM))) THEN
    POP_ASSUM SUBST1_TAC THEN
    SIMP_TAC bool_ss [INT_DIVIDES_LADD, INT_DIVIDES_LMUL,
                      INT_DIVIDES_REFL] THEN
    Q.SUBGOAL_THEN `1 = &d / &d` SUBST1_TAC THENL [
      ASM_SIMP_TAC bool_ss [INT_INJ, INT_DIV_ID],
      ALL_TAC
    ] THEN
    ASM_SIMP_TAC bool_ss [fractions, INT_DIVIDES_RMUL, INT_DIVIDES_REFL,
                          INT_INJ] THEN
    Q.SUBGOAL_THEN `&d + ~p * &a = q * &m` SUBST1_TAC THENL [
      REWRITE_TAC [INT_MUL_CALCULATE] THEN
      PROVE_TAC [eq_move_left_left],
      ALL_TAC
    ] THEN
    Q.SUBGOAL_THEN `b * (q * &m / &d) = &m * (q * b / &d)`
    (fn th => SUBST1_TAC th THEN
              SIMP_TAC bool_ss [INT_DIVIDES_LMUL, INT_DIVIDES_REFL]) THEN
    ASM_SIMP_TAC bool_ss [INT_MUL_DIV', INT_DIVIDES_LMUL, INT_DIVIDES_RMUL,
                          INT_INJ] THEN
    REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
    CONV_TAC (AC_CONV(INT_MUL_ASSOC, INT_MUL_COMM))
  ]);

val gcd1_thm = store_thm(
  "gcd1thm",
  ``!m n p q. (p * &m + q * &n = 1i) ==> (gcd m n = 1n)``,
  REPEAT STRIP_TAC THEN
  Q.SUBGOAL_THEN `&(gcd m n) int_divides (p * &m + q * &n)` ASSUME_TAC
  THENL [
    Q.SUBGOAL_THEN `&(gcd m n) int_divides (p * &m)`
    (REWRITE_TAC o C cons [] o MATCH_MP INT_DIVIDES_LADD) THENL [
       Q.SPEC_THEN `p` STRIP_ASSUME_TAC INT_NUM_CASES THEN
       FIRST_X_ASSUM SUBST_ALL_TAC THEN
       SIMP_TAC bool_ss [INT_NUM_DIVIDES, INT_MUL_CALCULATE,
                         INT_DIVIDES_NEG, INT_MUL_LZERO,
                         ALL_DIVIDES_0] THEN
       `divides (gcd m n) m` by PROVE_TAC [GCD_IS_GCD, is_gcd_def] THEN
       PROVE_TAC [DIVIDES_TRANS, DIVIDES_MULT, MULT_COMM],

       Q.SPEC_THEN `q` STRIP_ASSUME_TAC INT_NUM_CASES THEN
       FIRST_X_ASSUM SUBST_ALL_TAC THEN
       SIMP_TAC bool_ss [INT_NUM_DIVIDES, INT_MUL_CALCULATE,
                         INT_DIVIDES_NEG, INT_MUL_LZERO,
                         ALL_DIVIDES_0] THEN
       `divides (gcd m n) n` by PROVE_TAC [GCD_IS_GCD, is_gcd_def] THEN
       PROVE_TAC [DIVIDES_TRANS, DIVIDES_MULT, MULT_COMM]
    ],

    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC bool_ss [INT_DIVIDES_1, INT_EQ_CALCULATE]
  ]);

val gcd21_thm = store_thm(
  "gcd21_thm",
  ``!m a x b p q.
      (p * &a + q * &m = 1i) /\ ~(m = 0) /\ ~(a = 0) ==>
      (&m int_divides &a * x + b = ?t. x = ~p * b + t * &m)``,
  REPEAT STRIP_TAC THEN
  `1 = gcd a m` by PROVE_TAC [gcd1_thm] THEN
  `~(1n = 0)` by ASM_SIMP_TAC arith_ss []  THEN
  Q.PAT_ASSUM `x = 1i` (ASSUME_TAC o SYM) THEN
  Q.SPECL_THEN [`m`, `a`, `x`, `b`, `1`, `p`, `q`] MP_TAC gcdthm2 THEN
  REPEAT (FIRST_X_ASSUM (MP_TAC o SYM)) THEN
  ASM_SIMP_TAC bool_ss [INT_DIV_1, INT_DIVIDES_1]);


val elim_lt_coeffs1 = store_thm(
  "elim_lt_coeffs1",
  ``!n m x:int.  ~(m = 0) ==> (&n < &m * x = &n / &m < x)``,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC bool_ss [INT_DIV] THEN
  `0 < m` by ASM_SIMP_TAC arith_ss [] THEN
  POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `n` o MATCH_MP DIVISION) THEN
  Q.ABBREV_TAC `r = n MOD m` THEN
  Q.ABBREV_TAC `i = n DIV m` THEN
  EQ_TAC THEN STRIP_TAC THENL [
    SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [INT_NOT_LT]) THEN
    Q.SUBGOAL_THEN `&m * x <= &m * &i` ASSUME_TAC THENL [
      ASM_SIMP_TAC arith_ss [INT_LE_CALCULATE, INT_EQ_LMUL, INT_INJ,
                             GSYM lt_justify_multiplication, INT_LT] THEN
      ASM_SIMP_TAC bool_ss [GSYM INT_LE_CALCULATE],
      ALL_TAC
    ] THEN
    `&n < &i * &m` by PROVE_TAC [INT_LTE_TRANS, INT_MUL_COMM] THEN
    POP_ASSUM MP_TAC THEN ASM_SIMP_TAC arith_ss [INT_LT, INT_MUL],

    Q.SPEC_THEN `x` STRIP_ASSUME_TAC INT_NUM_CASES THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FULL_SIMP_TAC arith_ss [INT_LT, INT_INJ, INT_LT_CALCULATE, INT_MUL] THEN
    `i + 1 <= n'` by ASM_SIMP_TAC arith_ss [] THEN
    POP_ASSUM (MP_TAC o EQ_MP (Q.SPECL [`i + 1`, `n'`, `PRE m`]
                               MULT_LESS_EQ_SUC)) THEN
    `~(m = 0)` by ASM_SIMP_TAC arith_ss [] THEN POP_ASSUM MP_TAC THEN
    SIMP_TAC bool_ss [
      numLib.ARITH_PROVE ``~(x = 0) ==> (SUC (PRE x) = x)``] THEN
    Q.SUBGOAL_THEN `i * m = m * i` SUBST1_TAC THENL [
      CONV_TAC (AC_CONV(MULT_ASSOC, MULT_COMM)),
      ALL_TAC
    ] THEN
    MP_TAC (Q.ASSUME `r:num < m`) THEN
    SIMP_TAC bool_ss [LEFT_ADD_DISTRIB, MULT_CLAUSES] THEN
    numLib.ARITH_TAC
  ]);

val elim_lt_coeffs2 = store_thm(
  "elim_lt_coeffs2",
  ``!n m x:int. ~(m = 0) ==>
                 (&m * x < &n = x < if &m int_divides &n then &n / &m
                                    else &n / &m + 1)``,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC bool_ss [INT_DIV, INT_DIVIDES_MOD0, INT_INJ,
                        INT_MOD] THEN
  `0 < m` by ASM_SIMP_TAC arith_ss [] THEN
  POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `n` o MATCH_MP DIVISION) THEN
  Q.ABBREV_TAC `r = n MOD m` THEN
  Q.ABBREV_TAC `i = n DIV m` THEN
  `i * m = m * i` by CONV_TAC (AC_CONV(MULT_ASSOC, MULT_COMM)) THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  EQ_TAC THEN COND_CASES_TAC THEN STRIP_TAC THEN
  REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THENL [
    FULL_SIMP_TAC arith_ss [GSYM INT_MUL] THEN
    PROVE_TAC [lt_justify_multiplication, INT_LT],
    FULL_SIMP_TAC arith_ss [GSYM INT_MUL, GSYM INT_ADD] THEN
    `&m * &i + &r < &m * (&i + 1)` by
       ASM_SIMP_TAC bool_ss [INT_LDISTRIB, INT_LT_LADD, INT_LT,
                             INT_MUL_RID] THEN
    `&m * x < &m * (&i + 1)` by PROVE_TAC [INT_LT_TRANS] THEN
    `0i < &m` by ASM_SIMP_TAC arith_ss [INT_LT] THEN
    PROVE_TAC [lt_justify_multiplication],
    REWRITE_TAC [GSYM INT_MUL, GSYM INT_ADD, INT_ADD_RID] THEN
    PROVE_TAC [lt_justify_multiplication, INT_LT],
    `x <= &i` by ASM_SIMP_TAC bool_ss [GSYM INT_NOT_LT, not_less] THEN
    `&m * x <= &m * &i` by
       (FULL_SIMP_TAC bool_ss [INT_LE_CALCULATE, INT_EQ_LMUL, INT_INJ] THEN
        ASM_SIMP_TAC arith_ss [INT_LT, GSYM lt_justify_multiplication]) THEN
    `&m * &i < &(m * i + r)` by
       ASM_SIMP_TAC arith_ss [INT_LT, INT_MUL] THEN
    PROVE_TAC [INT_LET_TRANS]
  ]);

val elim_le_coeffs = store_thm(
  "elim_le_coeffs",
  ``!m n x.  0 < m ==> (0 <= m * x + n = 0 <= x + n/m)``,
  REPEAT STRIP_TAC THEN
  `~(m = 0) /\ ~(m < 0)` by PROVE_TAC [INT_LT_REFL, INT_LT_ANTISYM] THEN
  Q.SPEC_THEN `m` MP_TAC INT_DIVISION THEN
  ASM_SIMP_TAC arith_ss [] THEN
  DISCH_THEN (Q.SPEC_THEN `n` STRIP_ASSUME_TAC) THEN
  Q.ABBREV_TAC `q = n / m` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `r = n % m` THEN POP_ASSUM (K ALL_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SIMP_TAC arith_ss [INT_ADD_ASSOC, INT_MUL_COMM, GSYM INT_LDISTRIB] THEN
  EQ_TAC THEN STRIP_TAC THENL [
    `0 < m * (x + q) + m * 1` by
        (MATCH_MP_TAC INT_LET_TRANS THEN
         Q.EXISTS_TAC `m * (x + q) + r` THEN
         ASM_SIMP_TAC arith_ss [INT_LT_LADD, INT_MUL_RID]) THEN
    `0 < m * (x + q + 1)` by PROVE_TAC [INT_LDISTRIB] THEN
    `0 < x + q + 1` by PROVE_TAC [INT_LT_MONO, INT_MUL_RZERO] THEN
    PROVE_TAC [elim_minus_ones, int_sub, less_to_leq_samel],
    MATCH_MP_TAC INT_LE_TRANS THEN Q.EXISTS_TAC `m * (x + q)` THEN
    PROVE_TAC [INT_LE_MONO, INT_MUL_RZERO, INT_LE_ADDR]
  ]);

val elim_eq_coeffs = store_thm(
  "elim_eq_coeffs",
  ``!m x y.  ~(m = 0) ==>
             ((&m * x = y) = &m int_divides y /\ (x = y / &m))``,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC bool_ss [INT_DIVIDES] THEN EQ_TAC THEN STRIP_TAC THENL [
    POP_ASSUM (SUBST_ALL_TAC o SYM) THEN CONJ_TAC THENL [
      PROVE_TAC [INT_MUL_COMM],
      ALL_TAC
    ] THEN ONCE_REWRITE_TAC [INT_MUL_COMM] THEN
    ASM_SIMP_TAC bool_ss [INT_MUL_DIV, INT_INJ, INT_MOD_ID, INT_DIV_ID,
                          INT_MUL_RID],
    POP_ASSUM SUBST_ALL_TAC THEN POP_ASSUM (SUBST_ALL_TAC o SYM) THEN
    ASM_SIMP_TAC bool_ss [INT_MUL_DIV, INT_INJ, INT_MOD_ID, INT_DIV_ID,
                          INT_MUL_RID] THEN
    PROVE_TAC [INT_MUL_COMM]
  ]);


val int_acnorm_ss = SSFRAG{
  name = SOME "int_acnorm",
  ac = [(SPEC_ALL INT_ADD_ASSOC, SPEC_ALL INT_ADD_COMM),
        (SPEC_ALL INT_MUL_ASSOC, SPEC_ALL INT_MUL_COMM)],
  convs = [], congs = [], dprocs = [], filter = NONE,
  rewrs = []};

(* lemma 1 from Cooper's paper

     (d = gcd(um, an) = pum + qan) ==>
     ( m | ax + b /\ n | ux + v =
        mn | dx + bqn + vpm /\ d | av - ub )
*)
val adhoc_lemma = prove(
  ``!a b c.  a + (b - c) = (a - c) + b:int``,
  SIMP_TAC (bool_ss ++ int_acnorm_ss) [INT_SUB_CALCULATE]);
val adhoc_lemma2 = prove(
  ``!a b c.  a - b + c = a + (c - b:int)``,
  SIMP_TAC (bool_ss ++ int_acnorm_ss) [INT_SUB_CALCULATE]);


val cooper_lemma_1 = store_thm(
  "cooper_lemma_1",
  ``!m n a b u v p q x d.
       (d = gcd (u * m) (a * n)) /\
       (&d = p * &u * &m + q * &a * &n) /\
       ~(m = 0) /\ ~(n = 0) /\ ~(a = 0) /\ ~(u = 0) ==>
       (&m int_divides &a * x + b /\ &n int_divides &u * x + v =
        &m * &n int_divides &d * x + v * &m * p + b * &n * q /\
        &d int_divides &a * v - &u * b)``,
  REPEAT STRIP_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL [
    (* m | ax + b /\ n | ux + v ==> mn | dx + vmp + bnq *)
    `&m * &n int_divides (&a * x + b) * &n` by
        PROVE_TAC [INT_INJ, INT_DIVIDES_LRMUL] THEN
    `&m * &n int_divides (&u * x + v) * &m` by
        PROVE_TAC [INT_INJ, INT_MUL_COMM, INT_DIVIDES_LRMUL] THEN
    `&m * &n int_divides (&a * x + b) * &n * q` by
        PROVE_TAC [INT_DIVIDES_LMUL] THEN
    `&m * &n int_divides (&u * x + v) * &m * p` by
        PROVE_TAC [INT_DIVIDES_LMUL] THEN
    `&m * &n int_divides (&a * x + b) * &n * q + (&u * x + v) * &m * p` by
        PROVE_TAC [INT_DIVIDES_LADD] THEN
    `&m * &n int_divides &a * x * &n * q + b * &n * q +
                         &u * x * &m * p + v * &m * p` by
        (POP_ASSUM MP_TAC THEN
         SIMP_TAC bool_ss [INT_RDISTRIB, INT_ADD_ASSOC]) THEN
    `&m * &n int_divides (p * &u * &m + q * &a * &n) * x +
                         v * &m * p + b * &n * q` by
        (POP_ASSUM MP_TAC THEN
         SIMP_TAC (bool_ss ++ int_acnorm_ss)[INT_LDISTRIB, INT_RDISTRIB]) THEN
    POP_ASSUM MP_TAC THEN ASM_SIMP_TAC bool_ss [],
    (* m | ax + b /\ n | ux + v ==> d | av - ub *)
    `?j. &m * j = &a * x + b` by PROVE_TAC [INT_DIVIDES, INT_MUL_COMM] THEN
    `?k. &n * k = &u * x + v` by PROVE_TAC [INT_DIVIDES, INT_MUL_COMM] THEN
    `b = &m * j - &a * x` by
        PROVE_TAC [INT_EQ_SUB_LADD, INT_ADD_COMM] THEN
    `v = &n * k - &u * x` by
        PROVE_TAC [INT_EQ_SUB_LADD, INT_ADD_COMM] THEN
    `&u * b = &u * &m * j - &u * &a * x` by
        PROVE_TAC [INT_SUB_LDISTRIB, INT_MUL_ASSOC] THEN
    `&a * v = &a * &n * k - &a * &u * x` by
        PROVE_TAC [INT_SUB_LDISTRIB, INT_MUL_ASSOC] THEN
    `&a * v = &a * &n * k - &u * &a * x` by
        (POP_ASSUM MP_TAC THEN SIMP_TAC (bool_ss ++ int_acnorm_ss)[]) THEN
    `&a * v - &u * b = &a * &n * k - &u * &m * j` by
        ASM_SIMP_TAC bool_ss [INT_SUB_SUB3, INT_SUB_ADD] THEN
    `&d int_divides &u * &m /\ &d int_divides &a * &n` by
        PROVE_TAC [is_gcd_def, GCD_IS_GCD, INT_NUM_DIVIDES, INT_MUL] THEN
    `&d int_divides &u * &m * j /\ &d int_divides &a * &n * k` by
        PROVE_TAC [INT_DIVIDES_LMUL, INT_MUL_ASSOC] THEN
    `&d int_divides &a * &n * k - &u * &m * j` by
        PROVE_TAC [INT_DIVIDES_LSUB] THEN
    PROVE_TAC [],
    (* mn | dx + vmp + bnq /\ d | av - ub ==> m | ax + b *)
    Q.PAT_ASSUM `&m * &n int_divides &d * x + v * &m * p + b * &n * q`
       ASSUME_TAC THEN
    `&m * &n int_divides &m * p * (&u * x + v) + &n * q * (&a * x + b)` by
       (POP_ASSUM MP_TAC THEN
        ASM_SIMP_TAC (bool_ss ++ int_acnorm_ss)
                     [INT_LDISTRIB, INT_RDISTRIB]) THEN
    `&a * &u * &m * &n int_divides
         &u * &m * p * (&u * &a * x + &a * v) +
         &a * &n * q * (&u * &a * x + &u * b)` by
       (`~(&a * &u = 0)` by PROVE_TAC [INT_ENTIRE, INT_INJ, INT_MUL] THEN
        `(&a * &u) * (&m * &n) int_divides
             (&a * &u) * (&m * p * (&u * x + v) + &n * q * (&a * x + b))` by
           PROVE_TAC [INT_DIVIDES_LRMUL, INT_MUL_COMM] THEN
        POP_ASSUM MP_TAC THEN
        SIMP_TAC (bool_ss ++ int_acnorm_ss)[INT_LDISTRIB]) THEN
    `&a * &n * q = &d - &u * &m * p` by
       (FULL_SIMP_TAC (bool_ss ++ int_acnorm_ss) [] THEN
        PROVE_TAC [INT_EQ_SUB_RADD, INT_ADD_COMM]) THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE [INT_SUB_RDISTRIB, adhoc_lemma]) THEN
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE [GSYM INT_SUB_LDISTRIB,
                                          INT_ADD2_SUB2, INT_ADD_LID,
                                          INT_SUB_REFL,
                                          INT_MUL_RZERO]) THEN
    `&u * (&a * &m * &n) int_divides
        &u * (&m * p * (&a * v - &u * b) + &d * (&a * x + b))` by
      (POP_ASSUM MP_TAC THEN
       SIMP_TAC (bool_ss ++ int_acnorm_ss) [INT_LDISTRIB]) THEN
    `&a * &m * &n int_divides
         &m * p * (&a * v - &u * b) + &d * (&a * x + b)` by
       PROVE_TAC [INT_DIVIDES_LRMUL, INT_INJ, INT_MUL_COMM] THEN
    `?k. &d * k = &a * v - &u * b` by
       PROVE_TAC [INT_DIVIDES, INT_MUL_COMM] THEN
    `&d int_divides &a * &n` by
       PROVE_TAC [GCD_IS_GCD, is_gcd_def, INT_MUL, INT_NUM_DIVIDES] THEN
    `?l. &d * l = &a * &n` by
       PROVE_TAC [INT_DIVIDES, INT_MUL_COMM] THEN
    `&a * &m * &n int_divides
         &d * k * &m * p + &d * (&a * x + b)` by
       (Q.PAT_ASSUM `&a * &m * &n int_divides Y` MP_TAC THEN
        Q.PAT_ASSUM `&d * k = X` SUBST1_TAC THEN
        SIMP_TAC (bool_ss ++ int_acnorm_ss)[]) THEN
    `&d * l * &m int_divides
         &d * k * &m * p + &d * (&a * x + b)` by
       (POP_ASSUM MP_TAC THEN POP_ASSUM SUBST1_TAC THEN
        SIMP_TAC (bool_ss ++ int_acnorm_ss)[]) THEN
    `&m * l int_divides k * &m * p + (&a * x + b)` by
       (POP_ASSUM MP_TAC THEN
        `~(&d = 0)` by PROVE_TAC [INT_INJ, GCD_EQ_0, MULT_EQ_0] THEN
        REWRITE_TAC [GSYM INT_MUL_ASSOC, GSYM INT_LDISTRIB] THEN
        DISCH_THEN (MP_TAC o
                    CONV_RULE (BINOP_CONV (REWR_CONV INT_MUL_COMM))) THEN
        POP_ASSUM MP_TAC THEN
        SIMP_TAC (bool_ss ++ int_acnorm_ss) [INT_DIVIDES_LRMUL]) THEN
    `&m int_divides k * &m * p + (&a * x + b)` by
        PROVE_TAC [INT_DIVIDES_MUL, INT_DIVIDES_TRANS] THEN
    `&m int_divides k * &m * p` by
        PROVE_TAC [INT_DIVIDES_MUL, INT_MUL_COMM, INT_MUL_ASSOC] THEN
    PROVE_TAC [INT_DIVIDES_LADD],
    (* mn | dx + vmp + bnq /\ d | av - ub ==> n | ux + v *)
    Q.PAT_ASSUM `&m * &n int_divides &d * x + v * &m * p + b * &n * q`
       ASSUME_TAC THEN
    `&m * &n int_divides &m * p * (&u * x + v) + &n * q * (&a * x + b)` by
       (POP_ASSUM MP_TAC THEN
        ASM_SIMP_TAC (bool_ss ++ int_acnorm_ss)
                     [INT_LDISTRIB, INT_RDISTRIB]) THEN
    `&a * &u * &m * &n int_divides
         &u * &m * p * (&u * &a * x + &a * v) +
         &a * &n * q * (&u * &a * x + &u * b)` by
       (`~(&a * &u = 0)` by PROVE_TAC [INT_ENTIRE, INT_INJ, INT_MUL] THEN
        `(&a * &u) * (&m * &n) int_divides
             (&a * &u) * (&m * p * (&u * x + v) + &n * q * (&a * x + b))` by
           PROVE_TAC [INT_DIVIDES_LRMUL, INT_MUL_COMM] THEN
        POP_ASSUM MP_TAC THEN
        SIMP_TAC (bool_ss ++ int_acnorm_ss)[INT_LDISTRIB]) THEN
    `&u * &m * p = &d - &a * &n * q` by
       (FULL_SIMP_TAC (bool_ss ++ int_acnorm_ss) [] THEN
        PROVE_TAC [INT_EQ_SUB_RADD, INT_ADD_COMM]) THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE [INT_SUB_RDISTRIB, adhoc_lemma2]) THEN
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE [GSYM INT_SUB_LDISTRIB,
                                          INT_ADD2_SUB2, INT_ADD_LID,
                                          INT_SUB_REFL,
                                          INT_MUL_RZERO]) THEN
    `&a * (&u * &m * &n) int_divides
        &a * (&n * q * (&u * b - &a * v) + &d * (&u * x + v))` by
      (POP_ASSUM MP_TAC THEN
       SIMP_TAC (bool_ss ++ int_acnorm_ss) [INT_LDISTRIB]) THEN
    `&u * &m * &n int_divides
         &n * q * (&u * b - &a * v) + &d * (&u * x + v)` by
       PROVE_TAC [INT_DIVIDES_LRMUL, INT_INJ, INT_MUL_COMM] THEN
    `?k. &d * k = &u * b - &a * v` by
       PROVE_TAC [INT_DIVIDES, INT_MUL_COMM, INT_DIVIDES_NEG,
                  INT_NEG_SUB] THEN
    `&d int_divides &u * &m` by
       PROVE_TAC [GCD_IS_GCD, is_gcd_def, INT_MUL, INT_NUM_DIVIDES] THEN
    `?l. &d * l = &u * &m` by
       PROVE_TAC [INT_DIVIDES, INT_MUL_COMM] THEN
    `&u * &m * &n int_divides
         &d * k * &n * q + &d * (&u * x + v)` by
       (Q.PAT_ASSUM `&u * &m * &n int_divides Y` MP_TAC THEN
        Q.PAT_ASSUM `&d * k = X` SUBST1_TAC THEN
        SIMP_TAC (bool_ss ++ int_acnorm_ss)[]) THEN
    `&d * l * &n int_divides
         &d * k * &n * q + &d * (&u * x + v)` by
       (POP_ASSUM MP_TAC THEN POP_ASSUM SUBST1_TAC THEN
        SIMP_TAC (bool_ss ++ int_acnorm_ss)[]) THEN
    `&n * l int_divides k * &n * q + (&u * x + v)` by
       (POP_ASSUM MP_TAC THEN
        `~(&d = 0)` by PROVE_TAC [INT_INJ, GCD_EQ_0, MULT_EQ_0] THEN
        REWRITE_TAC [GSYM INT_MUL_ASSOC, GSYM INT_LDISTRIB] THEN
        DISCH_THEN (MP_TAC o
                    CONV_RULE (BINOP_CONV (REWR_CONV INT_MUL_COMM))) THEN
        POP_ASSUM MP_TAC THEN
        SIMP_TAC (bool_ss ++ int_acnorm_ss) [INT_DIVIDES_LRMUL]) THEN
    `&n int_divides k * &n * q + (&u * x + v)` by
        PROVE_TAC [INT_DIVIDES_MUL, INT_DIVIDES_TRANS] THEN
    `&n int_divides k * &n * q` by
        PROVE_TAC [INT_DIVIDES_MUL, INT_MUL_COMM, INT_MUL_ASSOC] THEN
    PROVE_TAC [INT_DIVIDES_LADD]
  ]);

val bmarker_def = new_definition(
  "bmarker_def",
  ``bmarker (b:bool) = b``);

val bmarker_rewrites = store_thm(
  "bmarker_rewrites",
  ``!p q r. (q /\ bmarker p = bmarker p /\ q) /\
            (q /\ (bmarker p /\ r) = bmarker p /\ (q /\ r)) /\
            ((bmarker p /\ q) /\ r = bmarker p /\ (q /\ r))``,
  REWRITE_TAC [bmarker_def] THEN tautLib.TAUT_TAC);

val positive_mod_part = prove(
  ``!p q r. 0 < q /\ 0 <= r /\ r < q ==>
            ((p * q + r) % q = r)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_MOD_UNIQUE THEN
  ASM_SIMP_TAC bool_ss [INT_LT_GT] THEN PROVE_TAC []);

infix 8 on
val int_ss = srw_ss() ++ numSimps.ARITH_ss
val tac1 =
    Q.EXISTS_TAC `&n - r` THEN
    ASM_SIMP_TAC bool_ss [INT_LE_SUB_LADD, INT_LE_SUB_RADD, move_sub,
                          INT_LE_LADD] THEN
    `0 < r` by FULL_SIMP_TAC bool_ss [INT_LE_LT] THEN
    FULL_SIMP_TAC int_ss [GSYM INT_ADD_ASSOC, INT_SUB_ADD2,
                           less_to_leq_samer, INT_ADD_COMM] THEN
    SUBST_ALL_TAC on
      (`&n + q * &n = (q + 1) * &n`,
       SIMP_TAC bool_ss [INT_ADD_COMM, INT_RDISTRIB, INT_MUL_LID]) THEN
    ASM_SIMP_TAC int_ss [INT_MOD_COMMON_FACTOR]
val tac2 =
    STRIP_TAC THEN REPEAT VAR_EQ_TAC THEN
    FULL_SIMP_TAC bool_ss [INT_ADD_RID] THEN
    POP_ASSUM MP_TAC THEN
    `0 <= i` by PROVE_TAC [INT_LE_TRANS, INT_LE_01] THEN
    `i < &n` by ASM_SIMP_TAC bool_ss [less_to_leq_samel, GSYM int_sub] THEN
    ASM_SIMP_TAC bool_ss [positive_mod_part] THEN
    STRIP_TAC THEN VAR_EQ_TAC THEN FULL_SIMP_TAC int_ss []
val NOT_INT_DIVIDES = store_thm(
  "NOT_INT_DIVIDES",
  ``!c d. ~(c = 0) ==>
          (~(c int_divides d) =
           ?i. 1 <= i /\ i <= ABS c - 1 /\ c int_divides d + i)``,
  REPEAT GEN_TAC THEN
  Q.SPEC_THEN `c` STRIP_ASSUME_TAC INT_NUM_CASES THEN
  ASM_SIMP_TAC bool_ss [INT_DIVIDES_NEG, INT_ABS_NUM, INT_ABS_NEG,
                        INT_NEG_EQ0] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC bool_ss [INT_DIVIDES_MOD0] THEN
  FIRST_ASSUM (MP_TAC o Q.SPEC `d` o MATCH_MP INT_DIVISION) THEN
  ASM_SIMP_TAC int_ss [INT_LT] THEN STRIP_TAC THEN
  Q.ABBREV_TAC `q = d / &n` THEN POP_ASSUM (K ALL_TAC) THEN
  Q.ABBREV_TAC `r = d % &n` THEN POP_ASSUM (K ALL_TAC) THEN
  EQ_TAC THEN STRIP_TAC THENL [tac1,tac2,tac1,tac2]);

val NOT_INT_DIVIDES_POS = store_thm(
  "NOT_INT_DIVIDES_POS",
  ``!n d. ~(n = 0) ==>
          (~(&n int_divides d) =
           ?i. (1 <= i /\ i <= &n - 1) /\ &n int_divides d + i)``,
  REPEAT STRIP_TAC THEN
  `~(&n = 0)` by ASM_SIMP_TAC bool_ss [INT_INJ] THEN
  ASM_SIMP_TAC bool_ss [NOT_INT_DIVIDES, INT_ABS_NUM, CONJ_ASSOC]);

val le_context_rwt1 = store_thm(
  "le_context_rwt1",
  ``0 <= c + x ==> x <= y ==> (0 <= c + y = T)``,
  PROVE_TAC [INT_LE_LADD, INT_ADD_COMM, INT_ADD_ASSOC, INT_LE_ADD2,
             INT_ADD_LID]);

val le_context_rwt2 = store_thm(
  "le_context_rwt2",
  ``0 <= c + x ==> y < ~x ==> (0 <= ~c + y = F)``,
  REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
  `c <= y` by PROVE_TAC [le_move_all_right, INT_ADD_COMM] THEN
  `~x <= c` by PROVE_TAC [INT_NEGNEG, le_move_all_right, INT_ADD_COMM] THEN
  PROVE_TAC [INT_LE_TRANS, INT_NOT_LE]);

val le_context_rwt3 = store_thm(
  "le_context_rwt3",
  ``0 <= c + x ==> x < y ==> ((0 = c + y) = F)``,
  REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
  PROVE_TAC [INT_LE_LADD, INT_LET_TRANS, INT_LT_REFL]);

val le_context_rwt4 = store_thm(
  "le_context_rwt4",
  ``0 <= c + x ==> x < ~y  ==> ((0 = ~c + y) = F)``,
  REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (SUBST_ALL_TAC o
             REWRITE_RULE [INT_NEG_0, INT_NEG_ADD, INT_NEGNEG] o
             AP_TERM ``$~ : int -> int``) THEN
  PROVE_TAC [INT_LE_LADD, INT_LET_TRANS, INT_LT_REFL]);

val le_context_rwt5 = store_thm(
  "le_context_rwt5",
  ``0 <= c + x ==> (0 <= ~c + ~x = (0 = c + x))``,
  STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE [INT_NEG_0, INT_NEG_ADD, INT_NEGNEG] o
               CONV_RULE (REWR_CONV (GSYM INT_LE_NEG))) THEN
    IMP_RES_TAC INT_LE_ANTISYM,
    POP_ASSUM (SUBST_ALL_TAC o
               REWRITE_RULE [INT_NEG_0, INT_NEG_ADD, INT_NEGNEG] o
               AP_TERM ``$~ : int -> int``) THEN
    REWRITE_TAC [INT_LE_REFL]
  ]);


val eq_context_rwt1 = store_thm(
  "eq_context_rwt1",
  ``(0i = c + x) ==> (0 <= c + y = x <= y)``,
  STRIP_TAC THEN ASM_REWRITE_TAC [INT_LE_LADD]);

val eq_context_rwt2 = store_thm(
  "eq_context_rwt2",
  ``(0 = c + x) ==> (0 <= ~c + y = ~x <= y)``,
  STRIP_TAC THEN
  POP_ASSUM (ASSUME_TAC o REWRITE_RULE [INT_NEG_0, INT_NEG_ADD] o
             AP_TERM ``$~ : int -> int``) THEN
  ASM_REWRITE_TAC [INT_LE_LADD]);

val _ = hide "bmarker";

val _ = export_theory();

end (* structure *)
