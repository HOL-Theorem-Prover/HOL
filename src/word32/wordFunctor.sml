functor wordFunctor (val bits : int) =
struct

(*
   app load ["bossLib","EquivType","pairTheory",
             "numeralTheory","selectUtil","abbrevUtil","bitsTheory"];
*)

infix 8 by;
infix THEN THENC THENL ++ |->;

open HolKernel boolLib abbrevUtil selectUtil Q Parse EquivType
     computeLib bossLib simpLib numLib pairTheory numeralTheory
     arithmeticTheory prim_recTheory bitsTheory;

val PROVE = fn thl => fn q => PROVE thl (Term q);

val _ = set_fixity "==" (Infixr 450);

val RIGHT_REWRITE_RULE =
     GEN_REWRITE_RULE (RAND_CONV o DEPTH_CONV) empty_rewrites;

(* -------------------------------------------------------- *)

val sbits = Int.toString bits;

val _ = new_theory ("word"^sbits);

(* -------------------------------------------------------- *)

val topbit = numSyntax.mk_numeral (Arbnum.fromInt (bits - 1));

val HB_def     = Define `HB = ^topbit`;

val WL_def     = Define `WL = SUC HB`;

val MODw_def   = Define `MODw n = n MOD 2 EXP WL`;

val INw_def    = Define `INw n = n < 2 EXP WL`;

val EQUIV_def  = xDefine "EQUIV" `x == y = (MODw x = MODw y)`;

val EQUIV_QT = store_thm("EQUIV_QT",
  `!x y. x == y = ($== x = $== y)`,
  REPEAT STRIP_TAC THEN EQ_TAC
    THEN B_RW_TAC [FUN_EQ_THM,EQUIV_def,MODw_def]
);

val EQUIV_SYM = PROVE [EQUIV_QT] `!x y. x == y = y == x`;

(* -------------------------------------------------------- *)

val WL_POS       = REWRITE_RULE [SYM WL_def] (SPEC `HB` LESS_0);

val WL_GEQ_ONE   = prove(`1 <= WL`,A_SIMP_TAC [WL_def,ADD1]);

val WL_SUB_ONE   = SIMP_CONV arith_ss [WL_def] (Term`WL - 1`);

val WL_SUB_HB    = SIMP_CONV bool_ss [SUC_SUB,WL_def] (Term`WL - HB`);

val WL_SUB_SUC_X = SIMP_CONV arith_ss [WL_def] (Term`WL - SUC x`);

(* -------------------------------------------------------- *)

val FUNPOW_THM = store_thm("FUNPOW_THM",
  `!f n x. FUNPOW f n (f x) = f (FUNPOW f n x)`,
  Induct_on `n` THEN ASM_REWRITE_TAC [FUNPOW]
);

val FUNPOW_THM2 = store_thm("FUNPOW_THM2",
  `!f n x. FUNPOW f (SUC n) x = f (FUNPOW f n x)`,
  Induct_on `n` THEN B_RW_TAC [FUNPOW,FUNPOW_THM]
);

val FUNPOW_COMP = store_thm("FUNPOW_COMP",
  `!f m n a. FUNPOW f m (FUNPOW f n a) = FUNPOW f (m + n) a`,
  Induct_on `n` THEN ASM_REWRITE_TAC [ADD_CLAUSES,FUNPOW]
);

(*
val FUNPOW_EVAL = store_thm("FUNPOW_EVAL",
  `!f n x. FUNPOW f n x = if n = 0 then x else FUNPOW f (n-1) (f x)`,
  Induct_on `n` THEN A_RW_TAC [FUNPOW]
);
*)

(* -------------------------------------------------------- *)

val INw_MODw = store_thm("INw_MODw",
  `!n. INw (MODw n)`,
  A_RW_TAC [ZERO_LT_TWOEXP,DIVISION,INw_def,MODw_def]
);

val TOw_IDEM = store_thm("TOw_IDEM",
  `!a. INw a ==> (MODw a = a)`,
  A_RW_TAC [INw_def,MODw_def,LESS_MOD]
);

val MODw_IDEM2 = store_thm("MODw_IDEM2",
  `!a. MODw (MODw a) = MODw a`,
  B_RW_TAC [INw_MODw,TOw_IDEM]
);

val TOw_QT = store_thm("TOw_QT",
  `!a. MODw a == a`,
  B_RW_TAC [EQUIV_def,MODw_IDEM2]
);

val MODw_THM = store_thm("MODw_THM",
  `MODw = BITS HB 0`,
  ONCE_REWRITE_TAC [FUN_EQ_THM]
    THEN REWRITE_TAC [MODw_def,WL_def,SPEC `HB` BITS_ZERO3]
);

(* -------------------------------------------------------- *)

val MOD_ADD = store_thm("MOD_ADD",
  `!a b. MODw (a + b) = MODw (MODw a + MODw b)`,
  B_RW_TAC [MODw_def,MOD_PLUS,ZERO_LT_TWOEXP]
);

val MODw_MULT = store_thm("MODw_MULT",
 `!a b. MODw (a * b) = MODw (MODw a * MODw b)`,
  B_RW_TAC [MODw_def,MOD_TIMES2,ZERO_LT_TWOEXP]
);

val AONE_def = Define `AONE = 1`;

val ADD_QT = store_thm("ADD_QT",
  `(!n. 0 + n == n) /\ !m n. SUC m + n == SUC (m + n)`,
  A_RW_TAC [EQUIV_def,ADD]
);

val ADD_0_QT = store_thm("ADD_0_QT",
  `!a. a + 0 == a`,
  A_RW_TAC [EQUIV_def]
);

val ADD_COMM_QT = store_thm("ADD_COMM_QT",
  `!a b. a + b == b + a`,
  A_RW_TAC [EQUIV_def]
);

val ADD_ASSOC_QT = store_thm("ADD_ASSOC_QT",
  `!a b c. a + (b + c) == a + b + c`,
  A_RW_TAC [EQUIV_def]
);

val MULT_QT = store_thm("MULT_QT",
  `(!n. 0 * n == 0) /\ !m n. SUC m * n == m * n + n`,
  A_RW_TAC [EQUIV_def,MULT]
);

val ADD1_QT = store_thm("ADD1_QT",
  `!m. SUC m == m + AONE`,
  A_RW_TAC [EQUIV_def,ADD1,AONE_def]
);

val ADD_CLAUSES_QT = store_thm("ADD_CLAUSES_QT",
  `(!m. 0 + m == m) /\ (!m. m + 0 == m) /\ (!m n. SUC m + n == SUC (m + n)) /\
      (!m n. m + SUC n == SUC (m + n))`,
  A_RW_TAC [EQUIV_def,ADD_CLAUSES]
);

val MODw_0 = (REWRITE_RULE [GSYM MODw_THM] o SPECL [`HB`,`0`]) BITS_ZERO2;
val SPEC_MOD_TIMES = (REWRITE_RULE [MULT_LEFT_1] o SPEC `1`
                        o REWRITE_RULE [ZERO_LT_TWOEXP] o SPEC `2 EXP WL`) MOD_TIMES;
val exp_gteq = REDUCE_RULE (MATCH_MP TWOEXP_MONO2 (SPEC `WL` ZERO_LESS_EQ));


val SUC_EQUIV_COMP = store_thm("SUC_EQUIV_COMP",
  `!a b. SUC a == b ==> a == (b + (2 EXP WL - 1))`,
  B_RW_TAC [EQUIV_def]
    THEN ONCE_REWRITE_TAC [MOD_ADD]
    THEN POP_ASSUM (fn th => REWRITE_TAC [SYM th])
    THEN B_SIMP_TAC [MODw_def,GSYM MOD_ADD,ADD1,GSYM LESS_EQ_ADD_SUB,exp_gteq]
    THEN A_SIMP_TAC [ONCE_REWRITE_RULE [ADD_COMM] SPEC_MOD_TIMES]
);

val INV_SUC_EQ_QT = store_thm("INV_SUC_EQ_QT",
  `!m n. (SUC m == SUC n) = (m == n)`,
  A_RW_TAC [EQUIV_def]
    THEN EQ_TAC
    THENL [
      B_RW_TAC []
        THEN IMP_RES_TAC (REWRITE_RULE [EQUIV_def] SUC_EQUIV_COMP)
        THEN R_FULL_SIMP_TAC [GSYM LESS_EQ_ADD_SUB,ADD1,MODw_def,exp_gteq]
        THEN REWRITE_TAC [ONCE_REWRITE_RULE [ADD_COMM] SPEC_MOD_TIMES],
      REWRITE_TAC [ADD1]
        THEN ONCE_REWRITE_TAC [MOD_ADD]
        THEN B_RW_TAC []
    ]
);

val ADD_INV_0_QT = store_thm("ADD_INV_0_QT",
  `!m n. (m + n == m) ==> (n == 0)`,
  Induct_on `m`
    THEN B_RW_TAC [ADD_CLAUSES]
    THEN B_FULL_SIMP_TAC [INV_SUC_EQ_QT]
);

val ADD_INV_0_EQ_QT = store_thm("ADD_INV_0_EQ_QT",
  `!m n. (m + n == m) = (n == 0)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC
    THEN IMP_RES_TAC ADD_INV_0_QT
    THEN B_FULL_SIMP_TAC [EQUIV_def]
    THEN ONCE_REWRITE_TAC [MOD_ADD]
    THEN ASM_A_SIMP_TAC [MODw_0,MODw_IDEM2]
);

val EQ_ADD_LCANCEL_QT = store_thm("EQ_ADD_LCANCEL_QT",
  `!m n p. (m + n == m + p) = (n == p)`,
  Induct_on `m` THEN ASM_REWRITE_TAC [ADD_CLAUSES,INV_SUC_EQ_QT]
);

val EQ_ADD_RCANCEL_QT = store_thm("EQ_ADD_RCANCEL_QT",
  `!m n p. (m + p == n + p) = (m == n)`,
  ONCE_REWRITE_TAC[ADD_COMM] THEN MATCH_ACCEPT_TAC EQ_ADD_LCANCEL_QT
);

val LEFT_ADD_DISTRIB_QT = store_thm("LEFT_ADD_DISTRIB_QT",
  `!m n p. p * (m + n) == p * m + p * n`,
  A_RW_TAC [EQUIV_def,LEFT_ADD_DISTRIB]
);

val MULT_ASSOC_QT = store_thm("MULT_ASSOC_QT",
  `!m n p. m * (n * p) == m * n * p`,
  A_RW_TAC [EQUIV_def,MULT_ASSOC]
);

val MULT_COMM_QT = store_thm("MULT_COMM_QT",
  `!m n. m * n == n * m`,
  A_RW_TAC [EQUIV_def,MULT_COMM]
);

val MULT_CLAUSES_QT = store_thm("MULT_CLAUSES_QT",
  `!m n. (0 * m == 0) /\ (m * 0 == 0) /\ (AONE * m == m) /\ (m * AONE == m) /\
         (SUC m * n == m * n + n) /\ (m * SUC n == m + m * n)`,
  A_RW_TAC [EQUIV_def,MULT_CLAUSES,AONE_def]
);

(* -------------------------------------------------------- *)

val MSBn_def = Define`MSBn = BIT HB`;
val ONE_COMP_def = Define`ONE_COMP x = 2 EXP WL - 1 - MODw x`;
val TWO_COMP_def = Define`TWO_COMP x = 2 EXP WL - MODw x`;

val MODw_LESS = REWRITE_RULE [MODw_def,INw_def] INw_MODw;

val ADD_TWO_COMP_QT = store_thm("ADD_TWO_COMP_QT",
  `!a. MODw a + TWO_COMP a == 0`,
  A_RW_TAC [TWO_COMP_def,EQUIV_def,MODw_def]
   THEN ASSUME_TAC (SPEC `a` MODw_LESS)
   THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
   THEN ASM_A_SIMP_TAC [GSYM LESS_EQ_ADD_SUB,ADD_SUB,ZERO_MOD,DIVMOD_ID,ZERO_LT_TWOEXP]
);

val TWO_COMP_ONE_COMP_QT = store_thm("TWO_COMP_ONE_COMP_QT",
  `!a. TWO_COMP a == ONE_COMP a + AONE`,
  STRIP_TAC THEN REWRITE_TAC [AONE_def]
    THEN ASSUME_TAC (SPEC `a` (REWRITE_RULE [INw_def] INw_MODw))
    THEN `1 + MODw a <= 2 EXP WL` by DECIDE_TAC
    THEN A_RW_TAC [EQUIV_def,ONE_COMP_def,TWO_COMP_def,SUB_RIGHT_SUB,SUB_RIGHT_ADD]
    THEN Cases_on `1 + MODw a = 2 EXP WL`
    THENL [
      RULE_ASSUM_TAC (SIMP_RULE bool_ss [GSYM SUC_ONE_ADD,GSYM PRE_SUC_EQ,ZERO_LT_TWOEXP])
        THEN ASM_R_SIMP_TAC [MODw_def,PRE_SUB1],
      R_FULL_SIMP_TAC []
    ]
);

(* -------------------------------------------------------- *)

(* |- !n a b. (!x. x <= n ==> (BIT x a = BIT x b)) = (BITS n 0 a = BITS n 0 b) *)
val BIT_BITS_THM_0 = (GEN `n` o SIMP_RULE arith_ss [] o SPECL [`n`,`0`]) BIT_BITS_THM;

(* |- !a b. (!x. x < WL ==> (BIT x a = BIT x b)) = a == b *)
val BIT_EQUIV_THM = save_thm("BIT_EQUIV_THM",
   SIMP_RULE bool_ss [BITS_ZERO3,GSYM MODw_def,GSYM WL_def,GSYM EQUIV_def,LESS_EQ_IMP_LESS_SUC,
                REWRITE_RULE [GSYM LESS_EQ,GSYM WL_def] (ONCE_REWRITE_CONV [GSYM LESS_EQ_MONO] (Term`x <= HB`))]
                    (SPEC `HB` BIT_BITS_THM_0)
);

(* -------------------------------------------------------- *)

(* |- !n h. SLICE h 0 n = BITS h 0 n *)
val SLICE_COR = (GEN_ALL o SIMP_RULE arithr_ss [] o SPECL [`n`,`h`,`0`]) SLICE_THM;

val BITS_SUC2 = store_thm("BITS_SUC2",
  `!n a. BITS (SUC n) 0 a = SLICE (SUC n) (SUC n) a + BITS n 0 a`,
  A_RW_TAC [GSYM SLICE_COR,SLICE_COMP_THM]
);

val lem = prove(
  `!n a. a < 2 EXP SUC n ==> ~(2 EXP SUC n < a + 1)`,
  A_RW_TAC [NOT_LESS,EXP]
);

val lem2 = MATCH_MP lem (REWRITE_RULE [SUB_0] (SPECL [`n`,`0`,`a`] BITSLT_THM));

val BITWISE_ONE_COMP_LEM = prove(
  `!n a b. BITWISE (SUC n) (\x y. ~x) a b = 2 EXP (SUC n) - 1 - BITS n 0 a`,
  Induct_on `n`
    THEN REPEAT STRIP_TAC
    THENL [
      R_RW_TAC [SBIT_def,BIT_def,BITWISE_def,NOT_BITS2],
      A_RW_TAC [BITWISE_def,SBIT_def,REWRITE_RULE [SLICE_THM] BITS_SUC2]
        THEN RULE_ASSUM_TAC (SIMP_RULE bool_ss [NOT_BIT,NOT_BITS,BIT_def])
        THEN ASM_A_SIMP_TAC [MULT_CLAUSES]
        THENL [
           Cases_on `2 EXP SUC n = BITS n 0 a + 1`
             THENL [
               ASM_A_SIMP_TAC [SUB_RIGHT_ADD,EXP],
               ASSUME_TAC lem2
                 THEN `~(2 EXP SUC n <= BITS n 0 a + 1)` by ASM_A_SIMP_TAC []
                 THEN ASM_A_SIMP_TAC [SUB_RIGHT_ADD,EXP]
             ],
           REWRITE_TAC [REWRITE_CONV [ADD_SUB,TIMES2] (Term`2 * a - a`),SUB_PLUS,EXP]
        ]
    ]
);

(* -------------------------------------------------------- *)

val BITWISE_ONE_COMP_THM = store_thm("BITWISE_ONE_COMP_THM",
  `!a b. BITWISE WL (\x y. ~x) a b = ONE_COMP a`,
  B_RW_TAC [WL_def,SPEC `HB` BITWISE_ONE_COMP_LEM,ONE_COMP_def,MODw_THM]
);

val ONE_COMP_THM = store_thm("ONE_COMP_THM",
  `!a x. x < WL ==> (BIT x (ONE_COMP a) = ~BIT x a)`,
  REWRITE_TAC [GSYM BITWISE_ONE_COMP_THM] THEN B_RW_TAC [BITWISE_THM]
);

val ZERO_IS_FALSE = prove(
  `!x. ~BIT x 0`,
  A_RW_TAC [BIT_def,BITS_THM,ZERO_LT_TWOEXP,ZERO_DIV,ZERO_MOD]
);

(* ONE_COMP_TRUE: |- !x. x < WL ==> BIT x (ONE_COMP 0) *)
val ONE_COMP_TRUE = REWRITE_RULE [ZERO_IS_FALSE] (SPEC `0` ONE_COMP_THM);

(* -------------------------------------------------------- *)

val OR_def    = Define `OR = BITWISE WL $\/`;
val AND_def   = Define `AND = BITWISE WL $/\`;
val EOR_def   = Define `EOR = BITWISE WL (\x y. ~(x = y))`;
val COMP0_def = Define `COMP0 = ONE_COMP 0`;

(* -------------------------------------------------------- *)

val BITWISE_THM2 = save_thm("BITWISE_THM2",
  (GEN `y` o GEN `op` o GEN `a` o GEN `b`)
  (SIMP_RULE bool_ss [BITWISE_THM] (SPECL [`BITWISE WL op a b`,`y`] BIT_EQUIV_THM))
);

val OR_ASSOC_QT = save_thm("OR_ASSOC_QT",
  (GEN `a` o GEN `b` o GEN `c`)
  (SIMP_RULE bool_ss [BITWISE_THM,DISJ_ASSOC,GSYM OR_def]
  (SPECL [`BITWISE WL $\/ (BITWISE WL $\/ a b) c`,`$\/`,`a`,`BITWISE WL $\/ b c`] BITWISE_THM2))
);

val OR_COMM_QT = save_thm("OR_COMM_QT",
  (GEN `a` o GEN `b`)
  (SIMP_RULE bool_ss [BITWISE_THM,DISJ_COMM,GSYM OR_def]
  (SPECL [`BITWISE WL ($\/) b a`,`$\/`,`a`,`b`] BITWISE_THM2))
);

val OR_ABSORB_QT = save_thm("OR_ABSORB_QT",
  (GEN `a` o GEN `b`)
  (SIMP_RULE bool_ss [BITWISE_THM,PROVE [] `!a b. a /\ (a \/ b) = a`,GSYM OR_def,GSYM AND_def]
  (SPECL [`a`,`$/\`,`a`,`BITWISE WL $\/ a b`] BITWISE_THM2))
);

val OR_IDEM_QT = save_thm("OR_IDEM_QT",
  GEN_ALL (SIMP_RULE bool_ss [OR_CLAUSES,GSYM OR_def] (SPECL [`a`,`$\/`,`a`,`a`] BITWISE_THM2))
);

val AND_ASSOC_QT = save_thm("AND_ASSOC_QT",
  (GEN `a` o GEN `b` o GEN `c`)
  (SIMP_RULE bool_ss [BITWISE_THM,CONJ_ASSOC,GSYM AND_def]
  (SPECL [`BITWISE WL $/\ (BITWISE WL $/\ a b) c`,`$/\`,`a`,`BITWISE WL $/\ b c`] BITWISE_THM2))
);

val AND_COMM_QT = save_thm("AND_COMM_QT",
  (GEN `a` o GEN `b`)
  (SIMP_RULE bool_ss [BITWISE_THM,CONJ_COMM,GSYM AND_def]
  (SPECL [`BITWISE WL $/\ b a`,`$/\`,`a`,`b`] BITWISE_THM2))
);

val AND_ABSORB_QT = save_thm("AND_ABSORB_QT",
  (GEN `a` o GEN `b`)
  (SIMP_RULE bool_ss [BITWISE_THM,PROVE [] `!a b. a \/ (a /\ b) = a`,GSYM AND_def,GSYM OR_def]
  (SPECL [`a`,`$\/`,`a`,`BITWISE WL $/\ a b`] BITWISE_THM2))
);

val AND_IDEM_QT = save_thm("AND_IDEM_QT",
  GEN_ALL (SIMP_RULE bool_ss [AND_CLAUSES,GSYM AND_def] (SPECL [`a`,`$/\`,`a`,`a`] BITWISE_THM2))
);

val OR_COMP_QT = save_thm("OR_COMP_QT",
  GEN_ALL (SIMP_RULE bool_ss [EXCLUDED_MIDDLE,ONE_COMP_TRUE,ONE_COMP_THM,GSYM OR_def,GSYM COMP0_def]
          (SPECL [`ONE_COMP 0`,`$\/`,`a`,`ONE_COMP a`] BITWISE_THM2))
);

val AND_COMP_QT = save_thm("AND_COMP_QT",
  GEN_ALL (SIMP_RULE bool_ss [ONE_COMP_THM,ZERO_IS_FALSE,GSYM AND_def]
          (SPECL [`0`,`$/\`,`a`,`ONE_COMP a`] BITWISE_THM2))
);

val ONE_COMP_QT = save_thm("ONE_COMP_QT",
  GEN_ALL (SIMP_RULE bool_ss [BITWISE_ONE_COMP_THM,ONE_COMP_THM]
          (SPECL [`a`,`\x y. ~x`,`ONE_COMP a`,`b`] BITWISE_THM2))
);

val RIGHT_AND_OVER_OR_QT = save_thm("RIGHT_AND_OVER_OR_QT",
  (GEN `a` o GEN `b` o GEN `c`)
  (SIMP_RULE bool_ss [BITWISE_THM,RIGHT_AND_OVER_OR,GSYM AND_def,GSYM OR_def]
  (SPECL [`BITWISE WL $\/ (BITWISE WL $/\ a c) (BITWISE WL $/\ b c)`,
          `$/\`,`BITWISE WL $\/ a b`,`c`] BITWISE_THM2))
);

val RIGHT_OR_OVER_AND_QT = save_thm("RIGHT_OR_OVER_AND_QT",
  (GEN `a` o GEN `b` o GEN `c`)
  (SIMP_RULE bool_ss [BITWISE_THM,RIGHT_OR_OVER_AND,GSYM AND_def,GSYM OR_def]
  (SPECL [`BITWISE WL $/\ (BITWISE WL $\/ a c) (BITWISE WL $\/ b c)`,
          `$\/`,`BITWISE WL $/\ a b`,`c`] BITWISE_THM2))
);

val DE_MORGAN_THM_QT1 =
  (SIMP_RULE bool_ss [BITWISE_THM,BITWISE_ONE_COMP_THM,ONE_COMP_THM,GSYM AND_def,GSYM OR_def]
  (SPECL [`ONE_COMP (BITWISE WL $/\ a b)`,
          `$\/`,`ONE_COMP a`,`ONE_COMP b`] BITWISE_THM2));

val DE_MORGAN_THM_QT2 =
  (SIMP_RULE bool_ss [BITWISE_THM,BITWISE_ONE_COMP_THM,ONE_COMP_THM,GSYM AND_def,GSYM OR_def]
  (SPECL [`ONE_COMP (BITWISE WL $\/ a b)`,
          `$/\`,`ONE_COMP a`,`ONE_COMP b`] BITWISE_THM2));

val DE_MORGAN_THM_QT = save_thm("DE_MORGAN_THM_QT",
  (GEN `a` o GEN `b`)
  (CONJ (ONCE_REWRITE_RULE [EQUIV_SYM] DE_MORGAN_THM_QT1)
        (ONCE_REWRITE_RULE [EQUIV_SYM] DE_MORGAN_THM_QT2))
);

(* -------------------------------------------------------- *)

val BIT_EQUIV = store_thm("BIT_EQUIV",
  `!n a b. n < WL ==> a == b ==> (BIT n a = BIT n b)`,
  B_RW_TAC [GSYM BIT_EQUIV_THM]
);

(* -------------------------------------------------------- *)

val HB_LESS_WL = REWRITE_RULE [SYM WL_def] (SPEC `HB` LESS_SUC_REFL);

val LSB_WELLDEF = store_thm("LSB_WELLDEF",
  `!a b. a == b ==> (LSBn a = LSBn b)`,
  B_RW_TAC [WL_POS,REDUCE_RULE (SPEC `0` BIT_EQUIV),LSBn_def]
);

val MSB_WELLDEF = store_thm("MSB_WELLDEF",
  `!a b. a == b ==> (MSBn a = MSBn b)`,
  B_RW_TAC [HB_LESS_WL,REDUCE_RULE (SPEC `HB` BIT_EQUIV),MSBn_def]
);

(* -------------------------------------------------------- *)

val BIT_SET_NOT_ZERO = prove(
  `!a. (a MOD 2 = 1) ==> (1 <= a)`,
  SPOSE_NOT_THEN STRIP_ASSUME_TAC
    THEN `a = 0` by DECIDE_TAC
    THEN A_FULL_SIMP_TAC [ZERO_MOD]
);

val BIT_SET_NOT_ZERO_COR = prove(
  `!x n op a b. x < n ==> op (BIT x a) (BIT x b) ==> (1 <= (BITWISE n op a b DIV 2 EXP x))`,
  REPEAT STRIP_TAC THEN ASM_B_SIMP_TAC [BITWISE_COR,BIT_SET_NOT_ZERO]
);

val BIT_SET_NOT_ZERO_COR2 = REWRITE_RULE [DIV1,EXP] (SPEC `0` BIT_SET_NOT_ZERO_COR);

val ADD_DIV_ADD_DIV2 = ONCE_REWRITE_RULE [MULT_COMM] (SIMP_RULE arith_ss [] (SPEC `2` ADD_DIV_ADD_DIV));

val BIT_DIV2 = prove(
  `!i. BIT n (i DIV 2) = BIT (SUC n) i`,
  R_RW_TAC [BIT_def,BITS_THM,EXP,ZERO_LT_TWOEXP,DIV_DIV_DIV_MULT]
);

val lemma1 = prove(
  `!a b n. 0 < n ==> ((a + SBIT b n) DIV 2 = a DIV 2 + SBIT b (n - 1))`,
  A_RW_TAC [SBIT_def]
    THEN IMP_RES_TAC LESS_ADD_1
    THEN A_FULL_SIMP_TAC [GSYM ADD1,ADD_DIV_ADD_DIV2,EXP]
);

val lemma2 = prove(
  `!b n. 2 * (SBIT b n) = SBIT b (n + 1)`,
  B_RW_TAC [MULT_CLAUSES,SBIT_def,GSYM ADD1,EXP]
);

val lemma3 = prove(
  `!n op a b. 0 < n ==> (BITWISE n op a b MOD 2 = SBIT (op (LSBn a) (LSBn b)) 0)`,
  B_RW_TAC [LSBn_def]
    THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC [MATCH_MP ((GSYM o SPEC `0`) BITWISE_THM) th])
    THEN B_RW_TAC [GSYM LSBn_def,LSB_ODD,ODD_MOD2_LEM,SBIT_def,EXP]
    THEN B_FULL_SIMP_TAC [GSYM NOT_MOD2_LEM]
);

val lemma4 = prove(
  `!n op a b. 0 < n /\ BITWISE n op a b <= SBIT (op (LSBn a) (LSBn b)) 0 ==>
              (BITWISE n op a b = SBIT (op (LSBn a) (LSBn b)) 0)`,
  A_RW_TAC [LSBn_def,SBIT_def,EXP]
    THEN IMP_RES_TAC BIT_SET_NOT_ZERO_COR2
    THEN ASM_A_SIMP_TAC []
);

val BITWISE_ISTEP = store_thm("BITWISE_ISTEP",
  `!n op a b. 0 < n ==> (BITWISE n op (a DIV 2) (b DIV 2) =
                        (BITWISE n op a b) DIV 2 + SBIT (op (BIT n a) (BIT n b)) (n - 1))`,
  Induct_on `n`
    THEN REPEAT STRIP_TAC
    THENL [
       A_FULL_SIMP_TAC [],
       Cases_on `n = 0`
         THENL [
            R_RW_TAC [BITWISE_def,SBIT_def,BIT_DIV2],
            B_FULL_SIMP_TAC [NOT_ZERO_LT_ZERO,BITWISE_def,SUC_SUB1,BIT_DIV2,lemma1]
         ]
    ]
);

val BITWISE_EVAL = store_thm("BITWISE_EVAL",
  `!n op a b. BITWISE (SUC n) op a b =
         2 * (BITWISE n op (a DIV 2) (b DIV 2)) + SBIT (op (LSBn a) (LSBn b)) 0`,
  REPEAT STRIP_TAC
    THEN Cases_on `n = 0`
    THENL [
       A_RW_TAC [BITWISE_def,MULT_CLAUSES,LSBn_def],
       A_FULL_SIMP_TAC [BITWISE_def,NOT_ZERO_LT_ZERO,BITWISE_ISTEP,
                        DIV_MULT_THM2,LEFT_ADD_DISTRIB,SUB_ADD,lemma2,lemma3]
         THEN A_RW_TAC [SUB_RIGHT_ADD,lemma4]
    ]
);

(* -------------------------------------------------------- *)

val MODw_2EXP_GT_WL = prove(
  `!n. WL <= n ==> (MODw (2 EXP n) = 0)`,
  B_RW_TAC [MODw_def]
    THEN IMP_RES_TAC LESS_EQ_EXP_MULT
    THEN ASM_B_SIMP_TAC [ZERO_LT_TWOEXP,MOD_EQ_0]
);

val BITWISE_WELLDEF = store_thm("BITWISE_WELLDEF",
  `!n op a b c d. a == b /\ c == d ==> (BITWISE n op) a c == (BITWISE n op) b d`,
  Induct_on `n`
    THEN REPEAT STRIP_TAC
    THENL [
       A_SIMP_TAC [BITWISE_def,EQUIV_def],
       FIRST_ASSUM (fn th => `!op. BITWISE n op a c == BITWISE n op b d` by
                        IMP_RES_TAC (SPECL [`op`,`a`,`b`,`c`,`d`] th))
         THEN ASM_B_SIMP_TAC [BITWISE_def]
         THEN Cases_on `n < WL`
         THENL [
            IMP_RES_TAC BIT_EQUIV THEN NTAC 4 (POP_ASSUM (K ALL_TAC))
              THEN A_RW_TAC [SBIT_def]
              THEN B_FULL_SIMP_TAC [EQUIV_def]
              THEN ONCE_REWRITE_TAC [MOD_ADD]
              THEN ASM_B_SIMP_TAC [],
            RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS])
              THEN A_RW_TAC [SBIT_def]
              THEN B_FULL_SIMP_TAC [EQUIV_def]
              THEN ONCE_REWRITE_TAC [MOD_ADD]
              THEN ASM_A_SIMP_TAC [MODw_IDEM2,MODw_2EXP_GT_WL]
         ]
    ]
);

val BITWISEw_WELLDEF = save_thm("BITWISEw_WELLDEF",SPEC `WL` BITWISE_WELLDEF);

val OR_WELLDEF  = REWRITE_RULE [GSYM OR_def]  (SPEC `$\/` BITWISEw_WELLDEF);
val AND_WELLDEF = REWRITE_RULE [GSYM AND_def] (SPEC `$/\` BITWISEw_WELLDEF);
val EOR_WELLDEF = REWRITE_RULE [GSYM EOR_def] (SPEC `(\x y. ~(x = y))` BITWISEw_WELLDEF);

(* -------------------------------------------------------- *)

val SUC_WELLDEF = store_thm("SUC_WELLDEF",
  `!a b. a == b ==> SUC a == SUC b`,
  B_RW_TAC [EQUIV_def,ADD1]
    THEN ONCE_REWRITE_TAC [MOD_ADD]
    THEN ASM_REWRITE_TAC []
);

val ADD_WELLDEF = store_thm("ADD_WELLDEF",
  `!a b c d. a == b /\ c == d ==> a + c == b + d`,
  B_RW_TAC [EQUIV_def]
    THEN ONCE_REWRITE_TAC [MOD_ADD]
    THEN ASM_REWRITE_TAC []
);


val MUL_WELLDEF = store_thm("MUL_WELLDEF",
  `!a b c d. a == b /\ c == d ==> a * c == b * d`,
  B_RW_TAC [EQUIV_def]
    THEN ONCE_REWRITE_TAC [MODw_MULT]
    THEN ASM_REWRITE_TAC []
);

val ONE_COMP_WELLDEF = store_thm("ONE_COMP_WELLDEF",
  `!a b. a == b ==> ONE_COMP a == ONE_COMP b`,
  B_RW_TAC [EQUIV_def,ONE_COMP_def]
);

val TWO_COMP_WELLDEF = store_thm("TWO_COMP_WELLDEF",
  `!a b. a == b ==> TWO_COMP a == TWO_COMP b`,
  B_RW_TAC [EQUIV_def,TWO_COMP_def]
);

val TOw_WELLDEF = store_thm("TOw_WELLDEF",
  `!a b. a == b ==> MODw a == MODw b`,
  B_RW_TAC [EQUIV_def]
);

(* -------------------------------------------------------- *)

val LSR_ONE_def = Define `LSR_ONE a = MODw a DIV 2`;
val ASR_ONE_def = Define `ASR_ONE a = LSR_ONE a + SBIT (MSBn a) HB`;
val ROR_ONE_def = Define `ROR_ONE a = LSR_ONE a + SBIT (LSBn a) HB`;
val RRXn_def    = Define `RRXn c a  = LSR_ONE a + SBIT c HB`;

val LSR_ONE_WELLDEF = store_thm("LSR_ONE_WELLDEF",
  `!a b. a == b ==> LSR_ONE a == LSR_ONE b`,
  B_RW_TAC [EQUIV_def,LSR_ONE_def]
);

val ASR_ONE_WELLDEF = store_thm("ASR_ONE_WELLDEF",
  `!a b. a == b ==> ASR_ONE a == ASR_ONE b`,
  B_RW_TAC [EQUIV_def,ASR_ONE_def,LSR_ONE_def]
    THEN IMP_RES_TAC (REWRITE_RULE [EQUIV_def] MSB_WELLDEF)
    THEN ASM_REWRITE_TAC []
);

val ROR_ONE_WELLDEF = store_thm("ROR_ONE_WELLDEF",
  `!a b. a == b ==> ROR_ONE a == ROR_ONE b`,
  B_RW_TAC [EQUIV_def,ROR_ONE_def,LSR_ONE_def]
    THEN IMP_RES_TAC (REWRITE_RULE [EQUIV_def] LSB_WELLDEF)
    THEN ASM_REWRITE_TAC []
);

val RRX_WELLDEF = store_thm("RRX_WELLDEF",
  `!a b c. a == b ==> (RRXn c) a == (RRXn c) b`,
  B_RW_TAC [EQUIV_def,RRXn_def,LSR_ONE_def]
);

(* -------------------------------------------------------- *)

val LSR_ONE_LEM = prove(
  `!n a. MODw a DIV 2 EXP n = BITS HB n a`,
  REPEAT STRIP_TAC
    THEN ONCE_REWRITE_TAC [GSYM (SIMP_RULE arith_ss [GSYM MODw_THM]
                                (SPECL [`HB`,`0`,`HB`,`n`] BITS_COMP_THM))]
    THEN REWRITE_TAC [SYM WL_def,GSYM MODw_def,MODw_IDEM2,BITS2_THM]
);

val LSR_ONE = store_thm("LSR_ONE",
  `LSR_ONE = BITS HB 1`,
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN STRIP_TAC
    THEN REWRITE_TAC [LSR_ONE_def,REWRITE_RULE [EXP_1] (SPEC `1` LSR_ONE_LEM)]
);

(* -------------------------------------------------------- *)

fun r(a,b,c,d) = {def_name=a,fixity=b,fname=c,func=d};

val [ADDw,ADD_0w,ADD1w,ADD_ASSOCw,ADD_CLAUSESw,
     ADD_COMMw,ADD_INV_0_EQw,EQ_ADD_LCANCELw,EQ_ADD_RCANCELw,
     LEFT_ADD_DISTRIBw,MULT_ASSOCw,MULT_COMMw,MULT_CLAUSESw,
     TOw_ELIM,ADD_TWO_COMP,TWO_COMP_ONE_COMP, OR_ASSOCw,OR_COMMw,
     OR_IDEMw,OR_ABSORBw,OR_COMPw,AND_ASSOCw,AND_COMMw,AND_IDEMw,
     AND_ABSORBw,AND_COMPw,ONE_COMPw,RIGHT_AND_OVER_ORw,RIGHT_OR_OVER_ANDw,
     DE_MORGAN_THMw]
 =
 define_equivalence_type
   {name = "word"^sbits,
    equiv = EQUIV_QT,
    defs = [r("w_0_def",Prefix,"w_0",(Term`0`)),
            r("w_1_def",Prefix,"w_1",(Term`AONE`)),
            r("w_T_def",Prefix,"w_T",(Term`COMP0`)),
            r("word_suc",Prefix,"word_suc",(Term`SUC`)),
            r("word_add",Infixl 500,"word_add",(Term`$+`)),
            r("word_mul",Infixl 550,"word_mul",(Term`$*`)),
            r("word_1comp",Prefix,"word_1comp",(Term`ONE_COMP`)),
            r("word_2comp",Prefix,"word_2comp",(Term`TWO_COMP`)),
            r("word_lsr1",Prefix,"word_lsr1",(Term`LSR_ONE`)),
            r("word_asr1",Prefix,"word_asr1",(Term`ASR_ONE`)),
            r("word_ror1",Prefix,"word_ror1",(Term`ROR_ONE`)),
            r("RRX_def",Prefix,"RRX",(Term`RRXn`)),
            r("LSB_def",Prefix,"LSB",(Term`LSBn`)),
            r("MSB_def",Prefix,"MSB",(Term`MSBn`)),
            r("bitwise_or" ,Infixl 600,"bitwise_or", (Term`OR`)),
            r("bitwise_eor",Infixl 600,"bitwise_eor",(Term`EOR`)),
            r("bitwise_and",Infixl 650,"bitwise_and",(Term`AND`)),
            r("TOw_def",Prefix,"TOw",(Term`MODw`))],
   welldefs = [SUC_WELLDEF,ADD_WELLDEF,MUL_WELLDEF,ONE_COMP_WELLDEF,
               TWO_COMP_WELLDEF,TOw_WELLDEF, OR_WELLDEF,AND_WELLDEF,
               EOR_WELLDEF,LSR_ONE_WELLDEF,ASR_ONE_WELLDEF,ROR_ONE_WELLDEF,
               RRX_WELLDEF],
   old_thms = [ADD_QT,ADD_0_QT,ADD1_QT,ADD_ASSOC_QT,ADD_CLAUSES_QT,
               ADD_COMM_QT,ADD_INV_0_EQ_QT, EQ_ADD_LCANCEL_QT,
               EQ_ADD_RCANCEL_QT,LEFT_ADD_DISTRIB_QT,MULT_ASSOC_QT,
               MULT_COMM_QT, MULT_CLAUSES_QT,TOw_QT,ADD_TWO_COMP_QT,
               TWO_COMP_ONE_COMP_QT,OR_ASSOC_QT,OR_COMM_QT,OR_IDEM_QT,
               OR_ABSORB_QT,OR_COMP_QT,AND_ASSOC_QT,AND_COMM_QT,AND_IDEM_QT,
               AND_ABSORB_QT,AND_COMP_QT,ONE_COMP_QT,RIGHT_AND_OVER_OR_QT,
               RIGHT_OR_OVER_AND_QT,DE_MORGAN_THM_QT]
  };

val _ = remove_termtok {term_name = "COND", tok = "=>"};

val _ = overload_on ("NOT", Term`$word_1comp`);

val _ = overload_on ("+", Term`$word_add`);
val _ = overload_on ("*", Term`$word_mul`);
val _ = overload_on ("&", Term`$bitwise_and`);
val _ = overload_on ("|", Term`$bitwise_or`);
val _ = overload_on ("#", Term`$bitwise_eor`);

val _ = add_infix("&",650,HOLgrammars.LEFT);
val _ = add_infix("|",625,HOLgrammars.LEFT);
val _ = add_infix("#",600,HOLgrammars.LEFT);
val _ = add_infix("<<",680,HOLgrammars.LEFT);
val _ = add_infix(">>",680,HOLgrammars.LEFT);
val _ = add_infix(">>>",680,HOLgrammars.LEFT);
val _ = add_infix("#>>",680,HOLgrammars.LEFT);

val bool_not = Term`$~`
val _ = overload_on ("~", Term`$word_2comp`);
val _ = overload_on ("~", bool_not);

val mk_word   = prim_mk_const {Name = "mk_word"^sbits,  Thy = "word"^sbits};
val dest_word = prim_mk_const {Name = "dest_word"^sbits,Thy = "word"^sbits};

val n2w_def = Define `n2w n = ^mk_word ($== n)`;
val w2n_def = Define `w2n w = MODw ($@ (^dest_word w))`;

val word_tybij = definition ("word"^sbits^"_tybij");
val mk_word_one_one  = BETA_RULE (prove_abs_fn_one_one word_tybij);
val word_abs_fn_onto = BETA_RULE (prove_abs_fn_onto word_tybij);

val _ = save_thm("ADDw",ADDw);
val _ = save_thm("ADD_0w",ADD_0w);
val _ = save_thm("ADD1w",ADD1w);
val _ = save_thm("ADD_ASSOCw",ADD_ASSOCw);
val _ = save_thm("ADD_CLAUSESw",ADD_CLAUSESw);
val _ = save_thm("ADD_COMMw",ADD_COMMw);
val _ = save_thm("ADD_INV_0_EQw",ADD_INV_0_EQw);
val _ = save_thm("EQ_ADD_LCANCELw",EQ_ADD_LCANCELw);
val _ = save_thm("EQ_ADD_RCANCELw",EQ_ADD_RCANCELw);
val _ = save_thm("LEFT_ADD_DISTRIBw",LEFT_ADD_DISTRIBw);
val _ = save_thm("MULT_ASSOCw",MULT_ASSOCw);
val _ = save_thm("MULT_COMMw",MULT_COMMw);
val _ = save_thm("MULT_CLAUSESw",MULT_CLAUSESw);
val _ = save_thm("TWO_COMP_ONE_COMP",TWO_COMP_ONE_COMP);
val _ = save_thm("OR_ASSOCw",OR_ASSOCw);
val _ = save_thm("OR_COMMw",OR_COMMw);
val _ = save_thm("OR_IDEMw",OR_IDEMw);
val _ = save_thm("OR_ABSORBw",OR_ABSORBw);
val _ = save_thm("AND_ASSOCw",AND_ASSOCw);
val _ = save_thm("AND_COMMw",AND_COMMw);
val _ = save_thm("AND_IDEMw",AND_IDEMw);
val _ = save_thm("AND_ABSORBw",AND_ABSORBw);
val _ = save_thm("ONE_COMPw",ONE_COMPw);
val _ = save_thm("RIGHT_AND_OVER_ORw",RIGHT_AND_OVER_ORw);
val _ = save_thm("RIGHT_OR_OVER_ANDw",RIGHT_OR_OVER_ANDw);
val _ = save_thm("DE_MORGAN_THMw",DE_MORGAN_THMw);

val THE_WL = SIMP_RULE arithr_ss [HB_def,ADD1] WL_def;

val w_T_def = definition "w_T_def";
val w_0 = save_thm("w_0",REWRITE_RULE [GSYM n2w_def] (definition "w_0_def"));
val w_1 = save_thm("w_1",REWRITE_RULE [GSYM n2w_def,AONE_def] (definition "w_1_def"));
val w_T = save_thm("w_T",SIMP_RULE arithr_ss [GSYM n2w_def,COMP0_def,ONE_COMP_def,MODw_def,THE_WL] w_T_def);

val ADD_TWO_COMP = save_thm("ADD_TWO_COMP",REWRITE_RULE [TOw_ELIM] ADD_TWO_COMP);
val ADD_TWO_COMP2 = save_thm("ADD_TWO_COMP2",ONCE_REWRITE_RULE [ADD_COMMw] ADD_TWO_COMP);

val word_add_def = definition "word_add";
val word_mul_def = definition "word_mul";
val word_1comp_def = definition "word_1comp";
val word_2comp_def = definition "word_2comp";
val word_lsr1_def = definition "word_lsr1";
val word_asr1_def = definition "word_asr1";
val word_ror1_def = definition "word_ror1";
val RRX_def = definition "RRX_def";
val LSB_def = definition "LSB_def";
val MSB_def = definition "MSB_def";
val bitwise_or_def = definition "bitwise_or";
val bitwise_eor_def = definition "bitwise_eor";
val bitwise_and_def = definition "bitwise_and";

(* -------------------------------------------------------- *)

val word_sub_def =
  new_infixl_definition
   ("word_sub",`$word_sub a b = a + ~b`,500);

val word_lsl_def =
  new_infixl_definition
   ("word_lsl",`$word_lsl a n = a * n2w (2 EXP n)`,680);

val word_lsr_def =
  new_infixl_definition
   ("word_lsr",`$word_lsr a n = FUNPOW word_lsr1 n a`,680);

val word_asr_def =
  new_infixl_definition
   ("word_asr",`$word_asr a n = FUNPOW word_asr1 n a`,680);

val word_ror_def =
  new_infixl_definition
   ("word_ror",`$word_ror a n = FUNPOW word_ror1 n a`,680);

val _ = overload_on ("-", Term`$word_sub`);
val _ = overload_on ("<<", Term`$word_lsl`);
val _ = overload_on (">>", Term`$word_asr`);
val _ = overload_on (">>>", Term`$word_lsr`);
val _ = overload_on ("#>>", Term`$word_ror`);

val BITw_def   = Define `BITw b n = BIT b (w2n n)`;
val BITSw_def  = Define `BITSw h l n = BITS h l (w2n n)`;
val SLICEw_def = Define `SLICEw h l n = SLICE h l (w2n n)`;

(* -------------------------------------------------------- *)

val ssd = SIMPSET {ac = [(SPEC_ALL ADD_ASSOCw, SPEC_ALL ADD_COMMw)],
                congs = [], convs = [], dprocs = [], filter = NONE, rewrs = []};

val word_ss = bool_ss++ssd;

val TWO_COMP_ADD = store_thm("TWO_COMP_ADD",
  `!a b. ~(a + b) = ~a + ~b`,
  let val rearrange = EQT_ELIM (SIMP_CONV word_ss []
                         (Term`~a + a + (~b + b) =
                           ~a + ~b + (a + b)`)) in
   REPEAT STRIP_TAC
     THEN `~a + a + (~b + b) = w_0`
       by REWRITE_TAC [ADD_TWO_COMP2,ADD_CLAUSESw]
     THEN RULE_ASSUM_TAC (REWRITE_RULE [rearrange])
     THEN ASSUME_TAC (SYM (SPEC `a + b` ADD_TWO_COMP2))
     THEN B_FULL_SIMP_TAC [EQ_ADD_RCANCELw]
  end
);

val TWO_COMP_ELIM = store_thm("TWO_COMP_ELIM",
  `!a. word_2comp (word_2comp a) = a`,
  STRIP_TAC
    THEN `~~a + ~a = a + ~a` by SIMP_TAC word_ss [ADD_TWO_COMP]
    THEN IMP_RES_TAC EQ_ADD_RCANCELw
);

val ADD_SUB_ASSOC = store_thm("ADD_SUB_ASSOC",
  `!a b c. a + b - c = a + (b - c)`,
  RW_TAC word_ss [word_sub_def]
);

val ADD_SUB_SYM = store_thm("ADD_SUB_SYM",
  `!a b c. a + b - c = a - c + b`,
  RW_TAC word_ss [word_sub_def]
);

val SUB_EQUALw = store_thm("SUB_EQUALw",
  `!a. a - a = w_0`,
   B_RW_TAC [word_sub_def,ADD_TWO_COMP]
);

val ADD_SUBw = store_thm("ADD_SUBw",
  `!a b. a + b - b = a`,
  B_RW_TAC [ADD_SUB_ASSOC,SUB_EQUALw,ADD_0w]
);

val SUB_ADDw = REWRITE_RULE [ADD_SUB_SYM] ADD_SUBw;

val SUB_SUBw = store_thm("SUB_SUBw",
  `!a b c. a - (b - c) = a + c - b`,
  RW_TAC word_ss [word_sub_def,TWO_COMP_ADD,TWO_COMP_ELIM]
);

val ONE_COMP_TWO_COMP = store_thm("ONE_COMP_TWO_COMP",
  `!a. NOT a = ~a - w_1`,
  B_RW_TAC [TWO_COMP_ONE_COMP,ADD_SUBw]
);

val SUBw = store_thm("SUBw",
  `!m n. word_suc m - n = word_suc (m - n)`,
  B_RW_TAC [ADD1w,ADD_SUB_SYM]
);

val ADD_EQ_SUBw = store_thm("ADD_EQ_SUBw",
  `!m n p. (m + n = p) = (m = p - n)`,
  REPEAT STRIP_TAC THEN EQ_TAC
    THEN B_RW_TAC [SUB_ADDw]
    THEN REWRITE_TAC [ADD_SUBw]
);

val CANCEL_SUBw = store_thm("CANCEL_SUBw",
  `!m n p. (n - p = m - p) = (n = m)`,
  REPEAT STRIP_TAC THEN EQ_TAC
    THEN B_RW_TAC [GSYM ADD_EQ_SUBw,ADD_SUBw,SUB_ADDw]
);

val SUB_PLUSw = store_thm("SUB_PLUSw",
  `!a b c. a - (b + c) = a - b - c`,
  RW_TAC word_ss [word_sub_def,TWO_COMP_ADD]
);

(* -------------------------------------------------------- *)

val word_nchotomy = store_thm("word_nchotomy",
  `!w. ?n. w = n2w n`,
  PROVE_TAC [n2w_def,word_abs_fn_onto]
);

val EQUIV_EXISTS = prove(`!y. ?x. $== y = $== x`, PROVE_TAC []);

(* |- (mk_word ($== x) = mk_word ($== y)) = ($== x = $== y) *)
val mk_word_eq_one_one = SIMP_RULE bool_ss [EQUIV_EXISTS] (SPECL [`$== x`,`$== y`] mk_word_one_one);

val dest_word_mk_word_eq = prove(
  `!a. ^dest_word (^mk_word ($== a)) = $== a`,
  STRIP_TAC THEN REWRITE_TAC [EQUIV_EXISTS,GSYM (BETA_RULE word_tybij)]
);

val dest_word_mk_word_eq2 = prove(
  `!a x. (^dest_word (^mk_word ($== a)) x) = (a == x)`,
  STRIP_TAC THEN REWRITE_TAC [dest_word_mk_word_eq]
);

(* |- !a. dest_word (mk_word ($== a)) = $== a *)
val dest_word_mk_word_eq3 = save_thm("dest_word_mk_word_eq3",
  (GEN_ALL o REWRITE_RULE [GSYM FUN_EQ_THM] o GEN `x` o SPEC_ALL) dest_word_mk_word_eq2
);

val dest_word_mk_word_exists = prove(
  `?x. ^dest_word (^mk_word ($== a)) x`,
  B_RW_TAC [dest_word_mk_word_eq2,EQUIV_def] THEN PROVE_TAC []
);

(* -------------------------------------------------------- *)

val etar = prove(
  `!p:num -> bool. $@p = @x. p x`,
  GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN PROVE_TAC []
);

val MODw_ELIM = store_thm("MODw_ELIM",
  `!n. n2w (MODw n) = n2w n`,
  B_RW_TAC [n2w_def,mk_word_eq_one_one]
    THEN ONCE_REWRITE_TAC [FUN_EQ_THM]
    THEN REWRITE_TAC [EQUIV_def,MODw_IDEM2]
);

val w2n_EVAL = store_thm("w2n_EVAL",
  `!n. w2n (n2w n) = MODw n`,
  B_RW_TAC [w2n_def,n2w_def]
    THEN ONCE_REWRITE_TAC [etar] THEN SELECT_TAC
    THEN B_RW_TAC [dest_word_mk_word_exists,dest_word_mk_word_eq2]
    THEN B_FULL_SIMP_TAC [EQUIV_def]
);

(* -------------------------------------------------------- *)

fun SELECT_WORD_TAC th1 th2 =
  B_SIMP_TAC [n2w_def,th1,mk_word_eq_one_one]
    THEN ONCE_REWRITE_TAC [etar] THEN SELECT_TAC
    THEN B_RW_TAC [dest_word_mk_word_exists,dest_word_mk_word_eq2]
    THEN ASM_B_SIMP_TAC [th2,EQUIV_SYM,GSYM EQUIV_QT];

val ADD_EVAL = store_thm("ADD_EVAL",
  `n2w a + n2w b = n2w (a + b)`,
  SELECT_WORD_TAC word_add_def ADD_WELLDEF);

val MUL_EVAL = store_thm("MUL_EVAL",
  `n2w a * n2w b = n2w (a * b)`,
  SELECT_WORD_TAC word_mul_def MUL_WELLDEF);

val ONE_COMP_EVAL = store_thm("ONE_COMP_EVAL",
  `NOT (n2w a) = n2w (ONE_COMP a)`,
  SELECT_WORD_TAC word_1comp_def ONE_COMP_WELLDEF);

val TWO_COMP_EVAL = store_thm("TWO_COMP_EVAL",
  `~(n2w a) = n2w (TWO_COMP a)`,
  SELECT_WORD_TAC word_2comp_def TWO_COMP_WELLDEF);

val LSR_ONE_EVAL = store_thm("LSR_ONE_EVAL",
  `word_lsr1 (n2w a) = n2w (LSR_ONE a)`,
  SELECT_WORD_TAC word_lsr1_def LSR_ONE_WELLDEF);

val ASR_ONE_EVAL = store_thm("ASR_ONE_EVAL",
  `word_asr1 (n2w a) = n2w (ASR_ONE a)`,
  SELECT_WORD_TAC word_asr1_def ASR_ONE_WELLDEF
);

val ROR_ONE_EVAL = store_thm("ROR_ONE_EVAL",
  `word_ror1 (n2w a) = n2w (ROR_ONE a)`,
  SELECT_WORD_TAC word_ror1_def ROR_ONE_WELLDEF
);

val RRX_EVAL = store_thm("RRX_EVAL",
  `RRX c (n2w a) = n2w (RRXn c a)`,
  SELECT_WORD_TAC RRX_def RRX_WELLDEF
);

val LSB_EVAL = store_thm("LSB_EVAL",
  `LSB (n2w a) = LSBn a`,
  SELECT_WORD_TAC LSB_def LSB_WELLDEF
);

val MSB_EVAL = store_thm("MSB_EVAL",
  `MSB (n2w a) = MSBn a`,
  SELECT_WORD_TAC MSB_def MSB_WELLDEF
);

val OR_EVAL = store_thm("OR_EVAL",
  `n2w a | n2w b = n2w (OR a b)`,
  SELECT_WORD_TAC bitwise_or_def OR_WELLDEF
);

val EOR_EVAL = store_thm("EOR_EVAL",
  `n2w a # n2w b = n2w (EOR a b)`,
  SELECT_WORD_TAC bitwise_eor_def EOR_WELLDEF
);

val AND_EVAL = store_thm("AND_EVAL",
  `n2w a & n2w b = n2w (AND a b)`,
  SELECT_WORD_TAC bitwise_and_def AND_WELLDEF
);

val BITS_EVAL = store_thm("BITS_EVAL",
  `!h l a. BITSw h l (n2w a) = BITS h l (MODw a)`,
  B_RW_TAC [BITSw_def,w2n_EVAL]
);

val BIT_EVAL = store_thm("BIT_EVAL",
  `!b a. BITw b (n2w a) = BIT b (MODw a)`,
  B_RW_TAC [BITw_def,w2n_EVAL]
);

val SLICE_EVAL = store_thm("SLICE_EVAL",
  `!h l a. SLICEw h l (n2w a) = SLICE h l (MODw a)`,
  B_RW_TAC [SLICEw_def,w2n_EVAL]
);

(* -------------------------------------------------------- *)

val LSL_ADD = store_thm("LSL_ADD",
  `!a m n. a << m << n = a << (m + n)`,
  B_RW_TAC [word_lsl_def,EXP_ADD,GSYM MULT_ASSOCw,MUL_EVAL]
);

val LSR_ADD = store_thm("LSR_ADD",
  `!a m n. a >>> m >>> n = a >>> (m + n)`,
  A_SIMP_TAC [word_lsr_def,FUNPOW_COMP]
);

val ASR_ADD = store_thm("ASR_ADD",
  `!a m n. a >> m >> n = a >> (m + n)`,
  A_SIMP_TAC [word_asr_def,FUNPOW_COMP]
);

val ROR_ADD = store_thm("ROR_ADD",
  `!a m n. a #>> m #>> n = a #>> (m + n)`,
  A_SIMP_TAC [word_ror_def,FUNPOW_COMP]
);

(* -------------------------------------------------------- *)

val n2w_TIMES = prove(
  `!a b. n2w (a * 2 EXP WL + b) = n2w b`,
  ONCE_REWRITE_TAC [GSYM MODw_ELIM]
    THEN B_SIMP_TAC [MODw_def,MOD_TIMES,ZERO_LT_TWOEXP]
);

val LSL_LIMIT = store_thm("LSL_LIMIT",
  `!w n.  HB < n ==> (w << n = w_0)`,
  B_RW_TAC [word_lsl_def]
    THEN IMP_RES_TAC LESS_ADD_1
    THEN RULE_ASSUM_TAC (REWRITE_RULE [GSYM ADD1,GSYM WL_def] o SIMP_RULE arith_ss [])
    THEN ASM_A_SIMP_TAC [(REWRITE_RULE [ADD_0,SYM w_0] o SPECL [`2 EXP p`,`0`]) n2w_TIMES,
                         EXP_ADD,MULT_CLAUSESw]
);

(* -------------------------------------------------------- *)

val MOD_MOD_DIV = store_thm("MOD_MOD_DIV",
  `!a b. INw (MODw a DIV 2 EXP b)`,
  A_RW_TAC [MODw_THM,BITS_DIV_THM]
    THEN ASSUME_TAC (SPECL [`HB`,`b`,`a`] BITSLT_THM)
    THEN ASSUME_TAC (SPECL [`SUC HB`,`b`] EXP_SUB_LESS_EQ)
    THEN IMP_RES_TAC LESS_LESS_EQ_TRANS
    THEN ASM_REWRITE_TAC [WL_def,INw_def]
);

val MOD_MOD_DIV_2EXP = store_thm("MOD_MOD_DIV_2EXP",
  `!a n. MODw (MODw a DIV 2 EXP n) DIV 2 = MODw a DIV 2 EXP SUC n`,
  A_RW_TAC [ZERO_LT_TWOEXP,DIV_DIV_DIV_MULT,TOw_IDEM,MOD_MOD_DIV,
            GSYM (ONCE_REWRITE_RULE [MULT_COMM] EXP)]
);

val LSR_EVAL = store_thm("LSR_EVAL",
  `!n. (n2w a) >>> n = n2w (MODw a DIV 2 EXP n)`,
  Induct_on `n`
    THENL [
       B_SIMP_TAC [FUNPOW,word_lsr_def,EXP,DIV1,MODw_ELIM],
       B_FULL_SIMP_TAC [word_lsr_def,FUNPOW_THM2,LSR_ONE_EVAL,LSR_ONE_def,MOD_MOD_DIV_2EXP]
    ]
);

val LSR_THM = store_thm("LSR_THM",
  `!x n. (n2w n) >>> x = n2w (BITS HB (MIN WL x) n)`,
  A_RW_TAC [LSR_EVAL,MODw_THM,BITS_DIV_THM,MIN_DEF,WL_def,BITS_ZERO]
);

val LSR_LIMIT = store_thm("LSR_LIMIT",
  `!x w. HB < x ==> (w >>> x = w_0)`,
  REPEAT STRIP_TAC
    THEN STRUCT_CASES_TAC (SPEC `w` word_nchotomy)
    THEN A_RW_TAC [LSR_THM,MIN_DEF,WL_def,BITS_ZERO,w_0]
);

(* -------------------------------------------------------- *)

val MOD_WL = (GEN_ALL o CONJUNCT2 o SPEC_ALL o REWRITE_RULE [WL_POS] o SPEC `WL`) DIVISION;

val n2w_TIMES2 = ONCE_REWRITE_RULE [ADD_COMM] n2w_TIMES;

val LEFT_SHIFT_LESS = store_thm("LEFT_SHIFT_LESS",
  `!n m a. a < 2 EXP m ==> 2 EXP n + a * 2 EXP n <= 2 EXP (m + n)`,
  A_RW_TAC [GSYM MULT,LESS_EQ,EXP_ADD,LESS_MONO_MULT]
);

val lem = prove(
  `!a b c d. a < b /\ b + c <= d ==> a + c < d`,
  A_RW_TAC []
);

val lem2 = prove(
  `!a b m n. a < 2 EXP n /\ b < 2 EXP m ==> a + b * 2 EXP n < 2 EXP (m + n)`,
  PROVE_TAC [LEFT_SHIFT_LESS,lem]
);

val lem3 = prove(
  `!a b h l. l <= h /\ a < 2 EXP (h - l) /\ b < 2 EXP l ==> a + b * 2 EXP (h - l) < 2 EXP h`,
  REPEAT STRIP_TAC
    THEN `a + b * 2 EXP (h - l) < 2 EXP (l + (h - l))` by IMP_RES_TAC (SPECL [`a`,`b`,`l`,`h - l`] lem2)
    THEN PAT_ASSUM `l <= h` (fn th => RULE_ASSUM_TAC (SIMP_RULE arith_ss [th,GSYM LESS_EQ_ADD_SUB]))
    THEN A_FULL_SIMP_TAC []
);

val lem4 = prove(
  `!x n. 0 < x MOD WL ==> INw (BITS HB (x MOD WL) n + BITS (x MOD WL - 1) 0 n * 2 EXP (WL - x MOD WL))`,
  B_RW_TAC [INw_def]
    THEN RULE_ASSUM_TAC (REWRITE_RULE [GSYM ONE,LESS_EQ])
    THEN POP_ASSUM (fn th =>
           ASSUME_TAC (SIMP_RULE arith_ss [th,ADD1,SUB_ADD] (SPECL [`x MOD WL - 1`,`0`,`n`] BITSLT_THM)))
    THEN ASSUME_TAC (REWRITE_RULE [GSYM WL_def] (SPECL [`HB`,`x MOD WL`,`n`] BITSLT_THM))
    THEN ASSUME_TAC (MATCH_MP LESS_IMP_LESS_OR_EQ (SPEC `x` MOD_WL))
    THEN ASM_B_SIMP_TAC [lem3]
);

val lem5 = prove(
  `!x n. MODw (BITS HB (x MOD WL) n + BITS (x MOD WL - 1) 0 n * 2 EXP (WL - x MOD WL)) =
          if x MOD WL = 0 then BITS HB 0 n
                          else BITS HB (x MOD WL) n + BITS (x MOD WL - 1) 0 n * 2 EXP (WL - x MOD WL)`,
  B_RW_TAC []
    THENL [
       A_SIMP_TAC [MOD_TIMES,ZERO_LT_TWOEXP,MOD_MOD,MODw_def,GSYM MODw_THM],
       RULE_ASSUM_TAC (REWRITE_RULE [NOT_ZERO_LT_ZERO])
         THEN ASM_B_SIMP_TAC [lem4,TOw_IDEM]
    ]
);

val lem6 = prove(
  `!h b n. (BITS b b n MOD 2 = 1) = BIT b n`,
  A_RW_TAC [GSYM ODD_MOD2_LEM,GSYM LSB_ODD,LSBn_def,BIT_def,BITS_COMP_THM]
);

val lem7 = PROVE [MULT_COMM,MULT_ASSOC] `!(a:num) b c. a * (b * c) = (a * c) * b`;

(* |- !n l h. BITS h l n DIV 2 = BITS h (l + 1) n *)
val BITS_DIV_THM2 = (REWRITE_RULE [EXP_1] o GEN_ALL o INST [`n` |-> `1`] o SPEC_ALL) BITS_DIV_THM;

(* |- !n. BITS 0 0 n = n MOD 2 *)
val BITS00 = GEN_ALL (REWRITE_CONV [SUC_SUB,DIV1,EXP,EXP_1,SYM TWO,BITS_THM] (Term`BITS 0 0 n`));

val SPEC_MOD_PLUS_1 = REWRITE_RULE [WL_POS] (SPEC `WL` MOD_PLUS_1);
val SPEC_MOD_ADD_1  = REWRITE_RULE [WL_POS] (SPEC `WL` MOD_ADD_1);

(* |- !n x. n #>> (SUC x) = word_ror1 (n #>> x) *)
val ROR_LEM = GEN_ALL (RIGHT_REWRITE_RULE [GSYM word_ror_def]
                 (SIMP_CONV bool_ss [word_ror_def,FUNPOW_THM2] (Term`n #>> (SUC x)`)));

val ROR_THM = store_thm("ROR_THM",
  `!x n. (n2w n) #>> x = let x' = x MOD WL in
                          n2w (BITS HB x' n + (BITS (x' - 1) 0 n) * 2 EXP (WL - x'))`,
  Induct_on `x`
    THEN REPEAT STRIP_TAC
    THENL [
      A_SIMP_TAC [ZERO_MOD,WL_POS,word_ror_def,FUNPOW,n2w_TIMES2,SYM MODw_THM,MODw_ELIM],
      POP_ASSUM (fn th => S_SIMP_TAC [th,ROR_LEM,ROR_ONE_EVAL,ROR_ONE_def,LSR_ONE_def])
        THEN Cases_on `(x + 1) MOD WL = 0`
        THENL [
           IMP_RES_TAC SPEC_MOD_PLUS_1
             THEN RULE_ASSUM_TAC (SIMP_RULE bool_ss [ADD_EQ_SUB,WL_GEQ_ONE,WL_SUB_ONE])
             THEN R_RW_TAC [lem5,lem6,ADD1,WL_SUB_HB,EXP_1,n2w_TIMES,n2w_TIMES2,MODw_THM,
                            MODw_ELIM,ADD_DIV_ADD_DIV,BITS_DIV_THM2,BITS_ZERO,
                            LSB_ODD,ODD_MOD2_LEM,MOD_TIMES]
             THENL [
               R_RW_TAC [SBIT_def,BIT_def] THEN B_FULL_SIMP_TAC [NOT_BITS2],
               IMP_RES_TAC NOT_ZERO_ADD1
                 THEN ASM_B_SIMP_TAC [SUC_SUB1,SIMP_RULE arith_ss [] (SPECL [`p`,`0`] BITS_SUC)]
             ],
           IMP_RES_TAC SPEC_MOD_ADD_1
             THEN A_RW_TAC [ADD1,BITS_DIV_THM2,WL_SUB_ONE,lem5]
             THENL [
               R_SIMP_TAC [lem7,WL_def,LSB_ODD,ODD_MOD2_LEM,EXP,MOD_TIMES]
                 THEN A_SIMP_TAC [GSYM BITS00,BITS_COMP_THM,GSYM BIT_def,SLICE_COR,
                                  REWRITE_RULE [ADD] (SPECL [`HB`,`0`] BIT_SLICE_LEM)],
               IMP_RES_TAC NOT_ZERO_ADD1 THEN POP_ASSUM (K ALL_TAC)
                 THEN POP_ASSUM (fn th => SIMP_TAC bool_ss [th,SUC_SUB1,WL_SUB_SUC_X,SUB_PLUS] THEN
                          ASSUME_TAC (REWRITE_RULE [th,WL_def,ADD1,LESS_MONO_ADD_EQ] (SPEC `x` MOD_WL)))
                 THEN IMP_RES_TAC LESS_ADD_1
                 THEN RULE_ASSUM_TAC (ONCE_REWRITE_RULE [ADD_COMM])
                 THEN ASM_A_SIMP_TAC [LSB_ODD,ODD_MOD2_LEM,GSYM ADD1,EXP,MOD_TIMES,
                                      lem7,BITS_DIV_THM2,ADD_DIV_ADD_DIV]
                 THEN A_SIMP_TAC [GSYM BITS00,BITS_COMP_THM,GSYM BIT_def,BIT_SLICE_LEM]
                 THEN B_SIMP_TAC [DECIDE (Term `a + SUC b = SUC a + b`),
                                  BIT_SLICE_LEM,ADD_ASSOC,GSYM RIGHT_ADD_DISTRIB,GSYM SLICE_COR]
                 THEN A_SIMP_TAC [ONCE_REWRITE_RULE [ADD_COMM] SLICE_COMP_THM]
             ]
        ]
    ]
);

val ROR_CYCLE = store_thm("ROR_CYCLE",
  `!x w. w #>> (x * WL) = w`,
  REPEAT STRIP_TAC
    THEN STRUCT_CASES_TAC (SPEC `w` word_nchotomy)
    THEN A_SIMP_TAC [MOD_EQ_0,WL_POS,ROR_THM,n2w_TIMES2,SYM MODw_THM,MODw_ELIM]
);

(* -------------------------------------------------------- *)

val lem = prove(
  `!x n. ~MSBn n ==> ~MSBn (BITS HB x n)`,
  A_RW_TAC [MSBn_def,BIT_def,MIN_DEF,BITS_COMP_THM2,BITS_ZERO]
    THEN `x = 0` by DECIDE_TAC
    THEN ASM_REWRITE_TAC [ADD]
);

val lem2 = prove(
  `!h l n. LSR_ONE (BITS HB l n) = BITS HB (SUC l) n`,
  A_RW_TAC [MIN_DEF,LSR_ONE,ADD1,BITS_COMP_THM2]
    THEN Cases_on `l = 0`
    THEN A_FULL_SIMP_TAC []
);

val lem3 = prove(
  `!n. ~MSBn n ==> (BITS HB HB n = 0)`,
  B_RW_TAC [BIT_def,MSBn_def,NOT_BITS2]
);

val lem4 = prove(
  `!n. MSBn n ==> (BITS HB HB n = 1)`,
  B_RW_TAC [MSBn_def,BIT_def]
);

val lem5 = prove(
  `!a b c. c < a /\ c < b ==> a - b + c < a`,
  A_RW_TAC [SUB_RIGHT_ADD]
);

val lem6 = prove(
  `!h x n. 2 EXP SUC h - 2 EXP (SUC h - x) + BITS h x n < 2 EXP SUC h`,
  REPEAT STRIP_TAC
    THEN ASSUME_TAC (SPECL [`h`,`x`,`n`] BITSLT_THM)
    THEN ASSUME_TAC (SPECL [`SUC h`,`x`] EXP_SUB_LESS_EQ)
    THEN IMP_RES_TAC LESS_LESS_EQ_TRANS
    THEN ASM_B_SIMP_TAC [lem5]
);

(* |- !x n. 2 EXP WL - 2 EXP (WL - x) + BITS HB x n < 2 EXP WL *)
val lem6b = REWRITE_RULE [GSYM WL_def] (SPEC `HB` lem6);

val lem6c = prove(
  `!h x n. 2 EXP h - 2 EXP (h - x) + BITS h (SUC x) n < 2 EXP h`,
  REPEAT STRIP_TAC
    THEN ASSUME_TAC (SIMP_RULE arith_ss [] (SPECL [`h`,`SUC x`,`n`] BITSLT_THM))
    THEN ASSUME_TAC (SPECL [`h`,`x`] EXP_SUB_LESS_EQ)
    THEN IMP_RES_TAC LESS_LESS_EQ_TRANS
    THEN ASM_B_SIMP_TAC [lem5]
);

val lem7 = prove(
  `!x n. LSR_ONE (2 EXP WL - 2 EXP (WL - x) + BITS HB x n) =
           (2 EXP WL - 2 EXP (WL - x) + BITS HB x n) DIV 2`,
  B_RW_TAC [LSR_ONE_def,MODw_THM,EXP,DIV1,REWRITE_RULE [GSYM WL_def] (SPEC `HB` BITS_LT_HIGH),lem6b]
);

val lem8 = prove(
  `!h x. x <= h ==> (2 EXP SUC h - 2 EXP (SUC h - x) = (2 EXP h - 2 EXP (h - x)) * 2)`,
  B_RW_TAC [ADD1,ONCE_REWRITE_RULE [ADD_COMM] LESS_EQ_ADD_SUB]
    THEN A_SIMP_TAC [GSYM ADD1,EXP,RIGHT_SUB_DISTRIB]
);

(* |- !x.  x <= HB ==> (2 EXP WL - 2 EXP (WL - x) = (2 EXP HB - 2 EXP (HB - x)) * 2) *)
val lem8b = REWRITE_RULE [GSYM WL_def] (SPEC `HB` lem8);

val lem8c = prove(
  `!x n. x <= HB ==> ((2 EXP WL - 2 EXP (WL - x) + BITS HB x n) DIV 2 =
                       2 EXP HB - 2 EXP (HB - x) + BITS HB (SUC x) n)`,
  A_RW_TAC [lem8b,ADD_DIV_ADD_DIV,ZERO_LT_TWOEXP,REWRITE_RULE [GSYM ADD1] BITS_DIV_THM2]
);

val lem9 = prove(
  `!x n. x <= HB /\ MSBn n ==> MSBn (2 EXP WL - 2 EXP (WL - x) + BITS HB x n)`,
  B_RW_TAC [MSBn_def,BIT_def,REWRITE_RULE [GSYM WL_def] (SPEC `HB` BITS_LT_HIGH),lem6b]
    THEN Cases_on `x = 0`
    THENL [
       ASM_A_SIMP_TAC [BITS_THM,CONJUNCT1 EXP,DIV1]
         THEN ASM_REWRITE_TAC [GSYM BITS2_THM],
       IMP_RES_TAC NOT_ZERO_ADD1
         THEN ASM_A_SIMP_TAC [EXP,WL_def]
         THEN B_SIMP_TAC [LESS_EQ_ADD_SUB,EXP_SUB_LESS_EQ,lem6c,TIMES2,GSYM ADD_ASSOC,DIV_MULT_1]
    ]
);

val lem10 = prove(
  `!a b. 2 EXP a <= 2 EXP (a - b) ==> (a = 0) \/ (b = 0)`,
  REPEAT STRIP_TAC
    THEN ASSUME_TAC (SPEC_ALL EXP_SUB_LESS_EQ)
    THEN `2 EXP (a - b) = 2 EXP a` by IMP_RES_TAC LESS_EQUAL_ANTISYM
    THEN A_FULL_SIMP_TAC [SUB_EQ_EQ_0,REDUCE_RULE (SPEC `2` EXP_INJECTIVE)]
);

val lem11 = (GEN_ALL o REWRITE_RULE [EXP,GSYM NOT_LESS_EQUAL])
              (MATCH_MP TWOEXP_MONO (DECIDE (Term `h < SUC h`)));

val TWOEXP_LT_EQ1 = prove(
  `!n. 2 EXP n <= 1 ==> (2 EXP n = 1)`,
  REPEAT STRIP_TAC THEN ASSUME_TAC (SPEC `n` ZERO_LT_TWOEXP) THEN DECIDE_TAC
);

(* |- !n x. n >> (SUC x) = word_asr1 (n >> x) *)
val ASR_LEM = GEN_ALL (RIGHT_REWRITE_RULE [GSYM word_asr_def]
                 (REWRITE_CONV [word_asr_def,FUNPOW_THM2] (Term`n >> (SUC x)`)));

val ASR_THM = store_thm("ASR_THM",
  `!x n. (n2w n) >> x =
           let x' = MIN HB x in
           let s = BITS HB x' n in
             n2w (if MSBn n then 2 EXP WL - 2 EXP (WL - x') + s else s)`,
  Induct_on `x`
    THEN REPEAT STRIP_TAC
    THENL [
      A_RW_TAC [word_asr_def,FUNPOW,MIN_DEF,SYM MODw_THM,MODw_ELIM],
      POP_ASSUM
        (fn th => S_RW_TAC [th,REDUCE_RULE (SPEC `F` SBIT_def),lem3,lem7,
                            lem,lem2,MIN_DEF,ASR_LEM,ASR_ONE_EVAL,ASR_ONE_def])
        THEN A_FULL_SIMP_TAC [BITS_ZERO,lem9,SBIT_def]
        THEN ASM_A_SIMP_TAC [lem8c,lem4,BITS_ZERO,WL_SUB_HB,WL_SUB_SUC_X]
        THENL [
          RW_TAC arithr_ss [WL_def,SUB_RIGHT_ADD,EXP,EXP_1,TWOEXP_LT_EQ1],
          `x = HB` by DECIDE_TAC
            THEN RW_TAC arithr_ss [WL_def,SUB_RIGHT_ADD,EXP,EXP_1,TWOEXP_LT_EQ1],
          RW_TAC arithr_ss [WL_def,SUB_RIGHT_ADD,EXP,EXP_SUB_LESS_EQ]
            THEN IMP_RES_TAC lem10
            THEN A_FULL_SIMP_TAC [lem11]
            THEN REWRITE_TAC [TIMES2]
            THEN ONCE_REWRITE_TAC [DECIDE (Term `(a:num) + b + c = a + c + b`)]
            THEN REWRITE_TAC [ADD_SUB]
        ]
    ]
);

val MIN_LEM = prove(
  `!a b. a <= b ==> (MIN a b = a)`,
  A_RW_TAC [MIN_DEF]
);

val ASR_LIMIT = store_thm("ASR_LIMIT",
  `!x w. HB <= x ==> (w >> x = if MSB w then w_T else w_0)`,
  REPEAT STRIP_TAC
    THEN STRUCT_CASES_TAC (SPEC `w` word_nchotomy)
    THEN A_RW_TAC [ASR_THM,MSB_EVAL,MSBn_def,BIT_def,MIN_LEM,NOT_BITS2,WL_SUB_HB,SUB_RIGHT_ADD,w_0,
                   REWRITE_RULE [ONE_COMP_def,COMP0_def,GSYM n2w_def,MODw_THM,BITS_ZERO2,SUB_0] w_T_def]
    THEN RULE_ASSUM_TAC (REWRITE_RULE [(SYM o REWRITE_RULE [GSYM (CONJUNCT2 EXP),SYM WL_def]
                                            o REWRITE_RULE [MULT_RIGHT_1,SYM TWO]
                                            o SPECL [`2 EXP HB`,`1`,`1`]) MULT_LESS_EQ_SUC])
    THEN ASSUME_TAC (SPEC `HB` ZERO_LT_TWOEXP)
    THEN `2 EXP HB = 1` by DECIDE_TAC
    THEN ASM_A_SIMP_TAC [WL_def,EXP]
);

(* -------------------------------------------------------- *)

val ZERO_SHIFT = store_thm("ZERO_SHIFT",
  `(!n. w_0 << n = w_0) /\ (!n. w_0 >> n = w_0) /\
   (!n. w_0 >>> n = w_0) /\ (!n. w_0 #>> n = w_0)`,
  A_RW_TAC [MUL_EVAL,word_lsl_def,w_0,ASR_THM,BITS_ZERO2,MSBn_def,BIT_def,LSR_THM,ROR_THM]
);

val ZERO_SHIFT2 = store_thm("ZERO_SHIFT2",
  `(!a. a << 0 = a) /\ (!a. a >> 0 = a) /\
   (!a. a >>> 0 = a) /\ (!a. a #>> 0 = a)`,
  A_RW_TAC [word_lsr_def,word_asr_def,word_ror_def,word_lsl_def,FUNPOW,GSYM w_1,MULT_CLAUSESw]
);

val lem = prove(
  `!n. (2 * n - 1) DIV 2 = n - 1`,
  Induct_on `n`
    THEN A_SIMP_TAC [ADD1,LEFT_ADD_DISTRIB,SUC_SUB1,ONCE_REWRITE_RULE [MULT_COMM] ADD_DIV_ADD_DIV]
);

val lem2 = PROVE [MULT_COMM,MULT_ASSOC] `!(a:num) b c. a * (b * c) = b * (a * c)`;

val lem3 = prove(
  `!m n. (2 EXP (m + n) - 1) DIV 2 EXP n = 2 EXP m - 1`,
  Induct_on `n`
    THEN A_FULL_SIMP_TAC [EXP_ADD,EXP,ZERO_LT_TWOEXP,GSYM DIV_DIV_DIV_MULT,DIV1,lem,lem2]
);

val lem3b = prove(
  `!m n. (2 EXP (m + n) - 1) MOD 2 EXP n = 2 EXP n - 1`,
  Induct_on `m`
    THEN STRIP_TAC
    THENL [
      A_SIMP_TAC [LESS_MOD,ZERO_LT_TWOEXP],
      B_SIMP_TAC [ADD_CLAUSES,EXP,TIMES2]
        THEN SUBST_OCCS_TAC [([1],SPECL [`m`,`n`,`2`] EXP_ADD)]
        THEN ASM_B_SIMP_TAC [MOD_TIMES,ZERO_LT_TWOEXP,LESS_EQ_ADD_SUB,
                             REWRITE_RULE [SYM ONE,LESS_EQ] ZERO_LT_TWOEXP]
    ]
);

val LSB_COMP0 = (SIMP_RULE arith_ss [WL_def,GSYM LSBn_def,SYM COMP0_def] o SPEC `0`) ONE_COMP_TRUE;
val MSB_COMP0 = (SIMP_RULE arith_ss [WL_def,GSYM MSBn_def,SYM COMP0_def] o SPEC `HB`) ONE_COMP_TRUE;

val lem4 = SIMP_RULE arith_ss [GSYM ADD1] (SPECL [`n`,`1`] lem3);
val lem5 = SIMP_RULE arith_ss [GSYM ADD1] (SPECL [`0`,`HB`] lem3b);

val ASR_w_T = store_thm("ASR_w_T",
  `!n. w_T >> n = w_T`,
  Induct_on `n`
    THENL [
      REWRITE_TAC [ZERO_SHIFT2],
      ASM_REWRITE_TAC [ASR_LEM,ASR_ONE_EVAL,w_T_def,GSYM n2w_def,ASR_ONE_def,LSR_ONE,BITS_THM,EXP_1,
                       SBIT_def,MSB_COMP0]
        THEN A_SIMP_TAC [COMP0_def,ONE_COMP_def,MODw_THM,BITS_ZERO2,WL_def,lem4,lem5]
        THEN REWRITE_TAC [EXP]
    ]
);

val ROR_w_T = store_thm("ROR_w_T",
  `!n. w_T #>> n = w_T`,
  Induct_on `n`
    THENL [
      REWRITE_TAC [ZERO_SHIFT2],
      ASM_REWRITE_TAC [ROR_LEM,ROR_ONE_EVAL,w_T_def,GSYM n2w_def,ROR_ONE_def,LSR_ONE,BITS_THM,EXP_1,
                       SBIT_def,LSB_COMP0]
        THEN A_SIMP_TAC [COMP0_def,ONE_COMP_def,MODw_THM,BITS_ZERO2,WL_def,lem4,lem5]
        THEN REWRITE_TAC [EXP]
    ]
);

(* -------------------------------------------------------- *)

val MODw_EVAL = save_thm("MODw_EVAL",
  GEN_ALL (SIMP_RULE arithr_ss [THE_WL] MODw_def)
);

val ADD_EVAL2 = save_thm("ADD_EVAL2",
  GEN_ALL (GEN_REWRITE_RULE (ONCE_DEPTH_CONV o RAND_CONV) empty_rewrites [GSYM MODw_ELIM] ADD_EVAL)
);

val MUL_EVAL2 = save_thm("MUL_EVAL2",
  GEN_ALL (GEN_REWRITE_RULE (ONCE_DEPTH_CONV o RAND_CONV) empty_rewrites [GSYM MODw_ELIM] MUL_EVAL)
);

val ONE_COMP_EVAL2 = save_thm("ONE_COMP_EVAL2",
  GEN_ALL (REWRITE_RULE [ONE_COMP_def,THE_WL] ONE_COMP_EVAL)
);

val TWO_COMP_EVAL2 = save_thm("TWO_COMP_EVAL2",
  GEN_ALL (REWRITE_RULE [TWO_COMP_def,THE_WL]
     (ONCE_REWRITE_RULE [GSYM (SPEC `TWO_COMP a` MODw_ELIM)] TWO_COMP_EVAL))
);

val LSR_ONE_EVAL2 = save_thm("LSR_ONE_EVAL2",
  GEN_ALL (REWRITE_RULE [LSR_ONE_def] LSR_ONE_EVAL)
);

val ASR_ONE_EVAL2 = save_thm("ASR_ONE_EVAL2",
  GEN_ALL (REWRITE_RULE [ASR_ONE_def,LSR_ONE_def,HB_def] ASR_ONE_EVAL)
);

val ROR_ONE_EVAL2 = save_thm("ROR_ONE_EVAL2",
  GEN_ALL (REWRITE_RULE [ROR_ONE_def,LSR_ONE_def,HB_def] ROR_ONE_EVAL)
);

val RRX_EVAL2 = save_thm("RRX_EVAL2",
  GEN_ALL (REWRITE_RULE [RRXn_def,LSR_ONE_def,HB_def] RRX_EVAL)
);

val LSB_EVAL2 = save_thm("LSB_EVAL2",GEN_ALL (REWRITE_RULE [LSB_ODD] LSB_EVAL));
val MSB_EVAL2 = save_thm("MSB_EVAL2",GEN_ALL (REWRITE_RULE [MSBn_def,HB_def] MSB_EVAL));

val OR_EVAL2  = save_thm("OR_EVAL2",GEN_ALL (SIMP_RULE bool_ss [OR_def,THE_WL] OR_EVAL));
val AND_EVAL2 = save_thm("AND_EVAL2",GEN_ALL (SIMP_RULE bool_ss [AND_def,THE_WL] AND_EVAL));
val EOR_EVAL2 = save_thm("EOR_EVAL2",GEN_ALL (SIMP_RULE bool_ss [EOR_def,THE_WL] EOR_EVAL));

(* -------------------------------------------------------- *)

val BITWISE_EVAL2 = store_thm("BITWISE_EVAL2",
  `!n op x y. BITWISE n op x y =
                 if n = 0 then 0
                 else 2 * BITWISE (n - 1) op (x DIV 2) (y DIV 2) +
                      (if op (ODD x) (ODD y) then 1 else 0)`,
  REPEAT STRIP_TAC
    THEN Cases_on `n = 0`
    THEN ASM_REWRITE_TAC [BITWISE_def]
    THEN IMP_RES_TAC NOT_ZERO_ADD1
    THEN A_FULL_SIMP_TAC [BITWISE_EVAL,SBIT_def,EXP,LSB_ODD]
);

(* -------------------------------------------------------- *)

val BITSwLT_THM = store_thm("BITSwLT_THM",
  `!h l n. BITSw h l n < 2 EXP (SUC h-l)`,
  B_RW_TAC [BITSLT_THM,BITSw_def]
);

val BITSw_COMP_THM = store_thm("BITSw_COMP_THM",
  `!h1 l1 h2 l2 n. h2 + l1 <= h1 ==> (BITS h2 l2 (BITSw h1 l1 n) = BITSw (h2+l1) (l2+l1) n)`,
  B_RW_TAC [BITSw_def,BITS_COMP_THM]
);

val BITSw_DIV_THM = store_thm("BITSw_DIV_THM",
  `!h l n x. (BITSw h l x) DIV 2 EXP n = BITSw h (l + n) x`,
  B_RW_TAC [BITSw_def,BITS_DIV_THM]
);

val BITw_THM = store_thm("BITw_THM",
  `!b n. BITw b n = (BITSw b b n = 1)`,
  B_RW_TAC [BITSw_def,BITw_def,BIT_def]
);

val SLICEw_THM = store_thm("SLICEw_THM",
  `!n h l. SLICEw h l n = BITSw h l n * 2 EXP l`,
  B_RW_TAC [SLICEw_def,BITSw_def,SLICE_THM]
);

val BITS_SLICEw_THM = store_thm("BITS_SLICEw_THM",
  `!h l n. BITS h l (SLICEw h l n) = BITSw h l n`,
  B_RW_TAC [SLICEw_def,BITSw_def,BITS_SLICE_THM]
);

val SLICEw_ZERO_THM = store_thm("SLICEw_ZERO_THM",
  `!n h. SLICEw h 0 n = BITSw h 0 n`,
  R_RW_TAC [SLICEw_THM]
);

val SLICEw_COMP_THM = store_thm("SLICEw_COMP_THM",
  `!h m l a. (SUC m) <= h /\ l <= m ==> (SLICEw h (SUC m) a + SLICEw m l a = SLICEw h l a)`,
  B_RW_TAC [SLICEw_def,SLICE_COMP_THM]
);

val BITSw_ZERO = store_thm("BITSw_ZERO",
  `!h l n. h < l ==> (BITSw h l n = 0)`,
  B_RW_TAC [BITSw_def,BITS_ZERO]
);

val SLICEw_ZERO = store_thm("SLICEw_ZERO",
  `!h l n. h < l ==> (SLICEw h l n = 0)`,
  B_RW_TAC [SLICEw_def,SLICE_ZERO]
);

(* -------------------------------------------------------- *)

val _ = export_theory();

(* -------------------------------------------------------- *)

end
