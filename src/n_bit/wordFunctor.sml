functor wordFunctor (val bits : int
                     val MLdir : string) =
struct

(*
   app load ["quotient","pairTheory", "metisLib",
             "numeralTheory","wordUtil","bitsTheory","numeral_bitsTheory"];
val bits = 8;
*)

open HolKernel Parse boolLib wordUtil Q quotient
     computeLib bossLib simpLib numLib pairTheory numeralTheory
     arithmeticTheory prim_recTheory bitsTheory metisLib;

val PROVE = fn thl => fn q => PROVE thl (Term q);

val RIGHT_REWRITE_RULE =
     GEN_REWRITE_RULE (RAND_CONV o DEPTH_CONV) empty_rewrites;

val std_ss = std_ss ++ rewrites [LET_THM]
val arith_ss = old_arith_ss ++ rewrites [LET_THM]

(* -------------------------------------------------------- *)

val sbits = Int.toString bits;

val _ = new_theory ("word"^sbits);

val _ = set_fixity "==" (Infixr 450);

(* -------------------------------------------------------- *)

val topbit = numSyntax.mk_numeral (Arbnum.fromInt (bits - 1));

fun Def s = curry Definition.new_definition s o Parse.Term;

val HB_def     = Def "HB_def" `HB = ^topbit`;

val WL_def     = Def "WL_def" `WL = SUC HB`;

val MOD_WL_def = Def "MOD_WL_def" `MOD_WL n = n MOD 2 EXP WL`;

val LT_WL_def  = Def "LT_WL_def" `LT_WL n = n < 2 EXP WL`;

val EQUIV_def  = Def "EQUIV_def" `x == y = (MOD_WL x = MOD_WL y)`;

val EQUIV_QT = prove(
  `!x y. x == y = ($== x = $== y)`,
  REPEAT STRIP_TAC THEN EQ_TAC
    THEN B_RW_TAC [FUN_EQ_THM,EQUIV_def,MOD_WL_def]
);

val EQUIV_REFL = PROVE [EQUIV_QT] `!x. x == x`;
val EQUIV_SYM = PROVE [EQUIV_QT] `!x y. x == y = y == x`;

(* -------------------------------------------------------- *)

val WL_POS       = REWRITE_RULE [SYM WL_def] (SPEC `HB` LESS_0);

val WL_GEQ_ONE   = prove(`1 <= WL`,A_SIMP_TAC [WL_def,ADD1]);

val WL_SUB_ONE   = SIMP_CONV arith_ss [WL_def] (Term`WL - 1`);

val WL_SUB_HB    = SIMP_CONV bool_ss [SUC_SUB,WL_def] (Term`WL - HB`);

val WL_SUB_SUC_X = SIMP_CONV arith_ss [WL_def] (Term`WL - SUC x`);

(* -------------------------------------------------------- *)

val LT_WL_MOD_WL = store_thm("LT_WL_MOD_WL",
  `!n. LT_WL (MOD_WL n)`,
  A_RW_TAC [ZERO_LT_TWOEXP,DIVISION,LT_WL_def,MOD_WL_def]
);

val MOD_WL_IDEM = store_thm("MOD_WL_IDEM",
  `!a. LT_WL a ==> (MOD_WL a = a)`,
  A_RW_TAC [LT_WL_def,MOD_WL_def,LESS_MOD]
);

val MOD_WL_IDEM2 = store_thm("MOD_WL_IDEM2",
  `!a. MOD_WL (MOD_WL a) = MOD_WL a`,
  B_RW_TAC [LT_WL_MOD_WL,MOD_WL_IDEM]
);

val MOD_WL_QT = prove(
  `!a. MOD_WL a == a`,
  B_RW_TAC [EQUIV_def,MOD_WL_IDEM2]
);

val MOD_WL_THM = store_thm("MOD_WL_THM",
  `MOD_WL = BITS HB 0`,
  ONCE_REWRITE_TAC [FUN_EQ_THM]
    THEN REWRITE_TAC [MOD_WL_def,WL_def,BITS_ZERO3]
);

(* -------------------------------------------------------- *)

val MOD_ADD = store_thm("MOD_ADD",
  `!a b. MOD_WL (a + b) = MOD_WL (MOD_WL a + MOD_WL b)`,
  B_RW_TAC [MOD_WL_def,MOD_PLUS,ZERO_LT_TWOEXP]
);

val MOD_WL_MULT = prove(
 `!a b. MOD_WL (a * b) = MOD_WL (MOD_WL a * MOD_WL b)`,
  B_RW_TAC [MOD_WL_def,MOD_TIMES2,ZERO_LT_TWOEXP]
);

val AONE_def = Def "AONE_def" `AONE = 1`;

val ADD_QT = prove(
  `(!n. 0 + n == n) /\ !m n. SUC m + n == SUC (m + n)`,
  A_RW_TAC [EQUIV_def,ADD]
);

val ADD_0_QT = prove(
  `!a. a + 0 == a`,
  A_RW_TAC [EQUIV_def]
);

val ADD_COMM_QT = prove(
  `!a b. a + b == b + a`,
  A_RW_TAC [EQUIV_def]
);

val ADD_ASSOC_QT = prove(
  `!a b c. a + (b + c) == a + b + c`,
  A_RW_TAC [EQUIV_def]
);

val MULT_QT = prove(
  `(!n. 0 * n == 0) /\ !m n. SUC m * n == m * n + n`,
  A_RW_TAC [EQUIV_def,MULT]
);

val ADD1_QT = prove(
  `!m. SUC m == m + AONE`,
  A_RW_TAC [EQUIV_def,ADD1,AONE_def]
);

val ADD_CLAUSES_QT = prove(
  `(!m. 0 + m == m) /\ (!m. m + 0 == m) /\ (!m n. SUC m + n == SUC (m + n)) /\
      (!m n. m + SUC n == SUC (m + n))`,
  A_RW_TAC [EQUIV_def,ADD_CLAUSES]
);

val MOD_WL_0 = (REWRITE_RULE [GSYM MOD_WL_THM] o SPECL [`HB`,`0`]) BITS_ZERO2;
val SPEC_MOD_TIMES = (REWRITE_RULE [MULT_LEFT_1] o SPEC `1` o
                      REWRITE_RULE [ZERO_LT_TWOEXP] o SPEC `2 EXP n`) MOD_TIMES;
val ONE_LT_EQ_TWOEXP = REWRITE_RULE [SYM ONE,LESS_EQ] ZERO_LT_TWOEXP;

val SUC_EQUIV_COMP = prove(
  `!a b. SUC a == b ==> a == (b + (2 EXP WL - 1))`,
  B_RW_TAC [EQUIV_def]
    THEN ONCE_REWRITE_TAC [MOD_ADD]
    THEN POP_ASSUM (fn th => REWRITE_TAC [SYM th])
    THEN B_SIMP_TAC [MOD_WL_def,GSYM MOD_ADD,ADD1,GSYM LESS_EQ_ADD_SUB,ONE_LT_EQ_TWOEXP]
    THEN A_SIMP_TAC [ONCE_REWRITE_RULE [ADD_COMM] SPEC_MOD_TIMES]
);

val INV_SUC_EQ_QT = prove(
  `!m n. (SUC m == SUC n) = (m == n)`,
  A_RW_TAC [EQUIV_def]
    THEN EQ_TAC
    THENL [
      B_RW_TAC []
        THEN IMP_RES_TAC (REWRITE_RULE [EQUIV_def] SUC_EQUIV_COMP)
        THEN A_FULL_SIMP_TAC [GSYM LESS_EQ_ADD_SUB,ADD1,MOD_WL_def,ONE_LT_EQ_TWOEXP]
        THEN REWRITE_TAC [ONCE_REWRITE_RULE [ADD_COMM] SPEC_MOD_TIMES],
      REWRITE_TAC [ADD1]
        THEN ONCE_REWRITE_TAC [MOD_ADD]
        THEN B_RW_TAC []
    ]
);

val ADD_INV_0_QT = prove(
  `!m n. (m + n == m) ==> (n == 0)`,
  Induct_on `m`
    THEN B_RW_TAC [ADD_CLAUSES]
    THEN B_FULL_SIMP_TAC [INV_SUC_EQ_QT]
);

val ADD_INV_0_EQ_QT = prove(
  `!m n. (m + n == m) = (n == 0)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC
    THEN IMP_RES_TAC ADD_INV_0_QT
    THEN B_FULL_SIMP_TAC [EQUIV_def]
    THEN ONCE_REWRITE_TAC [MOD_ADD]
    THEN ASM_A_SIMP_TAC [MOD_WL_0,MOD_WL_IDEM2]
);

val EQ_ADD_LCANCEL_QT = prove(
  `!m n p. (m + n == m + p) = (n == p)`,
  Induct_on `m` THEN ASM_REWRITE_TAC [ADD_CLAUSES,INV_SUC_EQ_QT]
);

val EQ_ADD_RCANCEL_QT = prove(
  `!m n p. (m + p == n + p) = (m == n)`,
  ONCE_REWRITE_TAC[ADD_COMM] THEN MATCH_ACCEPT_TAC EQ_ADD_LCANCEL_QT
);

val LEFT_ADD_DISTRIB_QT = prove(
  `!m n p. p * (m + n) == p * m + p * n`,
  A_RW_TAC [EQUIV_def,LEFT_ADD_DISTRIB]
);

val MULT_ASSOC_QT = prove(
  `!m n p. m * (n * p) == m * n * p`,
  A_RW_TAC [EQUIV_def,MULT_ASSOC]
);

val MULT_COMM_QT = prove(
  `!m n. m * n == n * m`,
  A_RW_TAC [EQUIV_def,MULT_COMM]
);

val MULT_CLAUSES_QT = prove(
  `!m n. (0 * m == 0) /\ (m * 0 == 0) /\ (AONE * m == m) /\ (m * AONE == m) /\
         (SUC m * n == m * n + n) /\ (m * SUC n == m + m * n)`,
  A_RW_TAC [EQUIV_def,MULT_CLAUSES,AONE_def]
);

(* -------------------------------------------------------- *)

val MSBn_def     = Def "MSBn_def"
                       `MSBn = BIT HB`;
val ONE_COMP_def = Def "ONE_COMP_def"
                       `ONE_COMP x = 2 EXP WL - 1 - MOD_WL x`;
val TWO_COMP_def = Def "TWO_COMP_def"
                       `TWO_COMP x = 2 EXP WL - MOD_WL x`;

val MOD_WL_LESS = REWRITE_RULE [MOD_WL_def,LT_WL_def] LT_WL_MOD_WL;

val WORD_ADD_RINV_QT = prove(
  `!a. MOD_WL a + TWO_COMP a == 0`,
  A_RW_TAC [TWO_COMP_def,EQUIV_def,MOD_WL_def]
   THEN ASSUME_TAC (SPEC `a` MOD_WL_LESS)
   THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
   THEN ASM_A_SIMP_TAC [GSYM LESS_EQ_ADD_SUB,ADD_SUB,ZERO_MOD,DIVMOD_ID,ZERO_LT_TWOEXP]
);

val WORD_NEG_QT = prove(
  `!a. TWO_COMP a == ONE_COMP a + AONE`,
  STRIP_TAC THEN REWRITE_TAC [AONE_def]
    THEN ASSUME_TAC (SPEC `a` (REWRITE_RULE [LT_WL_def] LT_WL_MOD_WL))
    THEN `1 + MOD_WL a <= 2 EXP WL` by DECIDE_TAC
    THEN A_RW_TAC [EQUIV_def,ONE_COMP_def,TWO_COMP_def,SUB_RIGHT_SUB,SUB_RIGHT_ADD]
    THEN Cases_on `1 + MOD_WL a = 2 EXP WL`
    THENL [
      RULE_ASSUM_TAC (SIMP_RULE bool_ss [GSYM SUC_ONE_ADD,GSYM PRE_SUC_EQ,ZERO_LT_TWOEXP])
        THEN ASM_A_SIMP_TAC [MOD_WL_def,PRE_SUB1],
      A_FULL_SIMP_TAC []
    ]
);

(* -------------------------------------------------------- *)

(* |- !n a b. (!x. x <= n ==> (BIT x a = BIT x b)) = (BITS n 0 a = BITS n 0 b) *)
val BIT_BITS_THM_0 = (GEN `n` o SIMP_RULE arith_ss [] o SPECL [`n`,`0`]) BIT_BITS_THM;

(* |- !a b. (!x. x < WL ==> (BIT x a = BIT x b)) = a == b *)
val BIT_EQUIV_THM =
   SIMP_RULE bool_ss [BITS_ZERO3,GSYM MOD_WL_def,GSYM WL_def,GSYM EQUIV_def,LESS_EQ_IMP_LESS_SUC,
                REWRITE_RULE [GSYM LESS_EQ,GSYM WL_def] (ONCE_REWRITE_CONV [GSYM LESS_EQ_MONO] (Term`x <= HB`))]
                    (SPEC `HB` BIT_BITS_THM_0);

(* -------------------------------------------------------- *)

val BITWISE_ONE_COMP_THM = store_thm("BITWISE_ONE_COMP_THM",
  `!a b. BITWISE WL (\x y. ~x) a b = ONE_COMP a`,
  B_RW_TAC [WL_def,SPEC `HB` BITWISE_ONE_COMP_LEM,ONE_COMP_def,MOD_WL_THM]
);

val ONE_COMP_BITWISE_THM = store_thm("ONE_COMP_BITWISE_THM",
  `!a. ONE_COMP a = BITWISE WL (\x y. ~x) a a`,
  METIS_TAC [BITWISE_ONE_COMP_THM]
);

val ONE_COMP_THM = store_thm("ONE_COMP_THM",
  `!a x. x < WL ==> (BIT x (ONE_COMP a) = ~BIT x a)`,
  REWRITE_TAC [GSYM BITWISE_ONE_COMP_THM] THEN B_RW_TAC [BITWISE_THM]
);

val ZERO_IS_FALSE = prove(
  `!x. ~BIT x 0`,
  A_RW_TAC [BIT_def,BITS_ZERO2]
);

(* ONE_COMP_TRUE: |- !x. x < WL ==> BIT x (ONE_COMP 0) *)
val ONE_COMP_TRUE = REWRITE_RULE [ZERO_IS_FALSE] (SPEC `0` ONE_COMP_THM);

(* -------------------------------------------------------- *)

val OR_def    = Def "OR_def"    `OR = BITWISE WL $\/`;
val AND_def   = Def "AND_def"   `AND = BITWISE WL $/\`;
val EOR_def   = Def "EOR_def"   `EOR = BITWISE WL (\x y. ~(x = y))`;
val COMP0_def = Def "COMP0_def" `COMP0 = ONE_COMP 0`;

(* -------------------------------------------------------- *)

val BITWISE_THM2 = (GEN `y` o GEN `op` o GEN `a` o GEN `b`)
  (SIMP_RULE bool_ss [BITWISE_THM] (SPECL [`BITWISE WL op a b`,`y`] BIT_EQUIV_THM));

val _ = save_thm("BITWISE_THM2",BITWISE_THM2);


val OR_ASSOC_QT = (GEN `a` o GEN `b` o GEN `c`)
  (SIMP_RULE bool_ss [BITWISE_THM,DISJ_ASSOC,GSYM OR_def]
  (SPECL [`BITWISE WL $\/ (BITWISE WL $\/ a b) c`,`$\/`,`a`,`BITWISE WL $\/ b c`] BITWISE_THM2));

val OR_COMM_QT = (GEN `a` o GEN `b`)
  (SIMP_RULE bool_ss [BITWISE_THM,DISJ_COMM,GSYM OR_def]
  (SPECL [`BITWISE WL ($\/) b a`,`$\/`,`a`,`b`] BITWISE_THM2));

val OR_ABSORB_QT = (GEN `a` o GEN `b`)
  (SIMP_RULE bool_ss [BITWISE_THM,PROVE [] `!a b. a /\ (a \/ b) = a`,GSYM OR_def,GSYM AND_def]
  (SPECL [`a`,`$/\`,`a`,`BITWISE WL $\/ a b`] BITWISE_THM2));

val OR_IDEM_QT =
  GEN_ALL (SIMP_RULE bool_ss [OR_CLAUSES,GSYM OR_def] (SPECL [`a`,`$\/`,`a`,`a`] BITWISE_THM2));

val AND_ASSOC_QT = (GEN `a` o GEN `b` o GEN `c`)
  (SIMP_RULE bool_ss [BITWISE_THM,CONJ_ASSOC,GSYM AND_def]
  (SPECL [`BITWISE WL $/\ (BITWISE WL $/\ a b) c`,`$/\`,`a`,`BITWISE WL $/\ b c`] BITWISE_THM2));

val AND_COMM_QT = (GEN `a` o GEN `b`)
  (SIMP_RULE bool_ss [BITWISE_THM,CONJ_COMM,GSYM AND_def]
  (SPECL [`BITWISE WL $/\ b a`,`$/\`,`a`,`b`] BITWISE_THM2));

val AND_ABSORB_QT = (GEN `a` o GEN `b`)
  (SIMP_RULE bool_ss [BITWISE_THM,PROVE [] `!a b. a \/ (a /\ b) = a`,GSYM AND_def,GSYM OR_def]
  (SPECL [`a`,`$\/`,`a`,`BITWISE WL $/\ a b`] BITWISE_THM2));

val AND_IDEM_QT =
  GEN_ALL (SIMP_RULE bool_ss [AND_CLAUSES,GSYM AND_def] (SPECL [`a`,`$/\`,`a`,`a`] BITWISE_THM2));

val EOR_ASSOC_QT = prove (
`!a b c. EOR a (EOR b c) == EOR (EOR a b) c`,
RW_TAC bool_ss [EOR_def, GSYM BITWISE_THM2, BITWISE_THM] THEN METIS_TAC []);

val EOR_COMM_QT = prove (
`!a b. EOR a b == EOR b a`,
RW_TAC bool_ss [EOR_def, GSYM BITWISE_THM2, BITWISE_THM] THEN METIS_TAC []);

val EOR_AND_OR_QT = prove (
`!a b. EOR a b == OR (AND a (ONE_COMP b)) (AND b (ONE_COMP a))`,
RW_TAC bool_ss [EOR_def, AND_def, OR_def, ONE_COMP_THM, GSYM BITWISE_THM2, BITWISE_THM]
THEN METIS_TAC []);

val EOR_ID_QT = prove (
`(!a. EOR a 0 == a) /\ (!a. EOR 0 a == a)`,
RW_TAC bool_ss [EOR_def, GSYM BITWISE_THM2, BITWISE_THM, BIT_ZERO]);

val EOR_INV_QT = prove (
`!a. EOR a a == 0`,
RW_TAC bool_ss [EOR_def, GSYM BITWISE_THM2, BITWISE_THM, BIT_ZERO]);

val OR_COMP_QT =
  GEN_ALL (SIMP_RULE bool_ss [EXCLUDED_MIDDLE,ONE_COMP_TRUE,ONE_COMP_THM,GSYM OR_def,GSYM COMP0_def]
          (SPECL [`ONE_COMP 0`,`$\/`,`a`,`ONE_COMP a`] BITWISE_THM2));

val AND_COMP_QT = GEN_ALL (SIMP_RULE bool_ss [ONE_COMP_THM,ZERO_IS_FALSE,GSYM AND_def]
          (SPECL [`0`,`$/\`,`a`,`ONE_COMP a`] BITWISE_THM2));

val ONE_COMP_QT = GEN_ALL (SIMP_RULE bool_ss [BITWISE_ONE_COMP_THM,ONE_COMP_THM]
          (SPECL [`a`,`\x y. ~x`,`ONE_COMP a`,`b`] BITWISE_THM2));

val RIGHT_AND_OVER_OR_QT = (GEN `a` o GEN `b` o GEN `c`)
  (SIMP_RULE bool_ss [BITWISE_THM,RIGHT_AND_OVER_OR,GSYM AND_def,GSYM OR_def]
  (SPECL [`BITWISE WL $\/ (BITWISE WL $/\ a c) (BITWISE WL $/\ b c)`,
          `$/\`,`BITWISE WL $\/ a b`,`c`] BITWISE_THM2));

val RIGHT_OR_OVER_AND_QT = (GEN `a` o GEN `b` o GEN `c`)
  (SIMP_RULE bool_ss [BITWISE_THM,RIGHT_OR_OVER_AND,GSYM AND_def,GSYM OR_def]
  (SPECL [`BITWISE WL $/\ (BITWISE WL $\/ a c) (BITWISE WL $\/ b c)`,
          `$\/`,`BITWISE WL $/\ a b`,`c`] BITWISE_THM2));

val DE_MORGAN_THM_QT1 =
  (SIMP_RULE bool_ss [BITWISE_THM,BITWISE_ONE_COMP_THM,ONE_COMP_THM,GSYM AND_def,GSYM OR_def]
  (SPECL [`ONE_COMP (BITWISE WL $/\ a b)`,
          `$\/`,`ONE_COMP a`,`ONE_COMP b`] BITWISE_THM2));

val DE_MORGAN_THM_QT2 =
  (SIMP_RULE bool_ss [BITWISE_THM,BITWISE_ONE_COMP_THM,ONE_COMP_THM,GSYM AND_def,GSYM OR_def]
  (SPECL [`ONE_COMP (BITWISE WL $\/ a b)`,
          `$/\`,`ONE_COMP a`,`ONE_COMP b`] BITWISE_THM2));

val DE_MORGAN_THM_QT = (GEN `a` o GEN `b`)
  (CONJ (ONCE_REWRITE_RULE [EQUIV_SYM] DE_MORGAN_THM_QT1)
        (ONCE_REWRITE_RULE [EQUIV_SYM] DE_MORGAN_THM_QT2));

(* -------------------------------------------------------- *)

val WORD_NEG_1_QT = prove(
  `TWO_COMP AONE == COMP0`,
  SIMP_TAC arith_ss [TWO_COMP_def,ONE_COMP_def,AONE_def,COMP0_def,
                    MOD_WL_def,ZERO_MOD,ZERO_LT_TWOEXP]
    THEN Cases_on `WL` THEN1 ASM_SIMP_TAC arith_ss [MOD_WL_def,EQUIV_def]
    THEN Q_TAC SUFF_TAC `1 < 2 ** SUC n` THEN1
           SRW_TAC [][LESS_MOD,EQUIV_REFL]
    THEN METIS_TAC [prim_recTheory.LESS_0, EXP, TWOEXP_MONO]
)

(* -------------------------------------------------------- *)

val BIT_EQUIV = prove(
  `!n a b. n < WL ==> a == b ==> (BIT n a = BIT n b)`,
  B_RW_TAC [GSYM BIT_EQUIV_THM]
);

(* -------------------------------------------------------- *)

val HB_LESS_WL = REWRITE_RULE [SYM WL_def] (SPEC `HB` LESS_SUC_REFL);

val LSB_WELLDEF = prove(
  `!a b. a == b ==> (LSBn a = LSBn b)`,
  B_RW_TAC [WL_POS,REDUCE_RULE (SPEC `0` BIT_EQUIV),LSBn_def]
);

val MSB_WELLDEF = prove(
  `!a b. a == b ==> (MSBn a = MSBn b)`,
  B_RW_TAC [HB_LESS_WL,REDUCE_RULE (SPEC `HB` BIT_EQUIV),MSBn_def]
);

(* -------------------------------------------------------- *)

val BITWISE_WELLDEF = prove(
  `!op a b c d. a == b /\ c == d ==> (BITWISE WL op) a c == (BITWISE WL op) b d`,
  RW_TAC bool_ss [WL_def,EQUIV_def,MOD_WL_THM]
    THEN ONCE_REWRITE_TAC [GSYM BITWISE_BITS] THEN ASM_REWRITE_TAC []
);

val OR_WELLDEF  = REWRITE_RULE [GSYM OR_def]  (SPEC `$\/` BITWISE_WELLDEF);
val AND_WELLDEF = REWRITE_RULE [GSYM AND_def] (SPEC `$/\` BITWISE_WELLDEF);
val EOR_WELLDEF = REWRITE_RULE [GSYM EOR_def] (SPEC `(\x y. ~(x = y))` BITWISE_WELLDEF);

(* -------------------------------------------------------- *)

val SUC_WELLDEF = prove(
  `!a b. a == b ==> SUC a == SUC b`,
  B_RW_TAC [EQUIV_def,ADD1]
    THEN ONCE_REWRITE_TAC [MOD_ADD]
    THEN ASM_REWRITE_TAC []
);

val ADD_WELLDEF = prove(
  `!a b c d. a == b /\ c == d ==> a + c == b + d`,
  B_RW_TAC [EQUIV_def]
    THEN ONCE_REWRITE_TAC [MOD_ADD]
    THEN ASM_REWRITE_TAC []
);


val MUL_WELLDEF = prove(
  `!a b c d. a == b /\ c == d ==> a * c == b * d`,
  B_RW_TAC [EQUIV_def]
    THEN ONCE_REWRITE_TAC [MOD_WL_MULT]
    THEN ASM_REWRITE_TAC []
);

val ONE_COMP_WELLDEF = prove(
  `!a b. a == b ==> ONE_COMP a == ONE_COMP b`,
  B_RW_TAC [EQUIV_def,ONE_COMP_def]
);

val TWO_COMP_WELLDEF = prove(
  `!a b. a == b ==> TWO_COMP a == TWO_COMP b`,
  B_RW_TAC [EQUIV_def,TWO_COMP_def]
);

val MOD_WL_WELLDEF = prove(
  `!a b. a == b ==> MOD_WL a == MOD_WL b`,
  B_RW_TAC [EQUIV_def]
);

(* -------------------------------------------------------- *)

val LSR_ONE_def = Def "LSR_ONE_def" `LSR_ONE a = MOD_WL a DIV 2`;
val ASR_ONE_def = Def "ASR_ONE_def" `ASR_ONE a = LSR_ONE a + SBIT (MSBn a) HB`;
val ROR_ONE_def = Def "ROR_ONE_def" `ROR_ONE a = LSR_ONE a + SBIT (LSBn a) HB`;
val RRXn_def    = Def "RRXn_def"    `RRXn c a  = LSR_ONE a + SBIT c HB`;

val LSR_ONE_WELLDEF = prove(
  `!a b. a == b ==> LSR_ONE a == LSR_ONE b`,
  B_RW_TAC [EQUIV_def,LSR_ONE_def]
);

val ASR_ONE_WELLDEF = prove(
  `!a b. a == b ==> ASR_ONE a == ASR_ONE b`,
  B_RW_TAC [EQUIV_def,ASR_ONE_def,LSR_ONE_def]
    THEN IMP_RES_TAC (REWRITE_RULE [EQUIV_def] MSB_WELLDEF)
    THEN ASM_REWRITE_TAC []
);

val ROR_ONE_WELLDEF = prove(
  `!a b. a == b ==> ROR_ONE a == ROR_ONE b`,
  B_RW_TAC [EQUIV_def,ROR_ONE_def,LSR_ONE_def]
    THEN IMP_RES_TAC (REWRITE_RULE [EQUIV_def] LSB_WELLDEF)
    THEN ASM_REWRITE_TAC []
);

val RRX_WELLDEF = prove(
  `!a b c. a == b ==> (RRXn c) a == (RRXn c) b`,
  B_RW_TAC [EQUIV_def,RRXn_def,LSR_ONE_def]
);

(* -------------------------------------------------------- *)

val LSR_ONE_LEM = prove(
  `!n a. MOD_WL a DIV 2 EXP n = BITS HB n a`,
  REPEAT STRIP_TAC
    THEN ONCE_REWRITE_TAC [GSYM (SIMP_RULE arith_ss [GSYM MOD_WL_THM]
                                (SPECL [`HB`,`0`,`HB`,`n`] BITS_COMP_THM))]
    THEN REWRITE_TAC [SYM WL_def,GSYM MOD_WL_def,MOD_WL_IDEM2,BITS_THM2]
);

val LSR_ONE = store_thm("LSR_ONE",
  `LSR_ONE = BITS HB 1`,
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN STRIP_TAC
    THEN REWRITE_TAC [LSR_ONE_def,REWRITE_RULE [EXP_1] (SPEC `1` LSR_ONE_LEM)]
);

(* -------------------------------------------------------- *)

fun r(a,b,c,d) = {def_name=a,fixity=b,fname=c,func=d};

val word_thms = define_equivalence_type
   {name = "word"^sbits,
    equiv = EQUIV_QT,
    defs = [r("word_0_def",Prefix,"word_0",(Term`0`)),
            r("word_1_def",Prefix,"word_1",(Term`AONE`)),
            r("word_T_def",Prefix,"word_T",(Term`COMP0`)),
            r("word_L_def",Prefix,"word_L",(Term`2 EXP HB`)),
            r("word_H_def",Prefix,"word_H",(Term`2 EXP HB - 1`)),
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
            r("word_id_def",Prefix,"word_id",(Term`MOD_WL`))],
   welldefs = [SUC_WELLDEF,ADD_WELLDEF,MUL_WELLDEF,ONE_COMP_WELLDEF,
               TWO_COMP_WELLDEF,MOD_WL_WELLDEF, OR_WELLDEF,AND_WELLDEF,
               EOR_WELLDEF,LSR_ONE_WELLDEF,ASR_ONE_WELLDEF,ROR_ONE_WELLDEF,
               RRX_WELLDEF,LSB_WELLDEF,MSB_WELLDEF],
   old_thms = [ADD_QT,ADD_0_QT,ADD1_QT,ADD_ASSOC_QT,ADD_CLAUSES_QT,
               ADD_COMM_QT,ADD_INV_0_EQ_QT, EQ_ADD_LCANCEL_QT,
               EQ_ADD_RCANCEL_QT,LEFT_ADD_DISTRIB_QT,MULT_ASSOC_QT,
               MULT_COMM_QT, MULT_CLAUSES_QT,MOD_WL_QT,WORD_ADD_RINV_QT,
               WORD_NEG_QT,WORD_NEG_1_QT,OR_ASSOC_QT,OR_COMM_QT,OR_IDEM_QT,
               OR_ABSORB_QT,OR_COMP_QT,AND_ASSOC_QT,AND_COMM_QT,AND_IDEM_QT,
               AND_ABSORB_QT,EOR_ASSOC_QT,EOR_COMM_QT,EOR_AND_OR_QT,EOR_ID_QT,EOR_INV_QT,
               AND_COMP_QT,ONE_COMP_QT,RIGHT_AND_OVER_OR_QT,
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
val _ = add_infix("#",625,HOLgrammars.LEFT);
val _ = add_infix("<<",680,HOLgrammars.LEFT);
val _ = add_infix(">>",680,HOLgrammars.LEFT);
val _ = add_infix(">>>",680,HOLgrammars.LEFT);
val _ = add_infix("#>>",680,HOLgrammars.LEFT);

val bool_not = Term`$~`
val _ = overload_on ("~", Term`$word_2comp`);
val _ = overload_on ("~", bool_not);

val thyname = "word"^sbits;

val mk_word    = prim_mk_const {Name = "word"^sbits^"_ABS",Thy = thyname};
val dest_word  = prim_mk_const {Name = "word"^sbits^"_REP",Thy = thyname};
val word_type = mk_thy_type{Tyop="word"^sbits, Thy=thyname,Args=[]};

val n2w_def = Def "n2w_def" `n2w n = ^mk_word n`;
val w2n_def = Def "w2n_def" `w2n w = MOD_WL (^dest_word w)`;

val _ = add_bare_numeral_form (#"w", SOME "n2w");

val word_QUOTIENT = REWRITE_RULE [quotientTheory.QUOTIENT_def,EQUIV_REFL]
                     (definition ("word"^sbits^"_QUOTIENT"));
val mk_word_one_one  = GSYM (CONJUNCT2 word_QUOTIENT);
val word_abs_fn_onto = CONJUNCT1 word_QUOTIENT;

val word_L_def = save_thm("word_L_def",REWRITE_RULE [GSYM n2w_def] (definition "word_L_def"));
val word_H_def = save_thm("word_H_def",REWRITE_RULE [GSYM n2w_def] (definition "word_H_def"));
val word_T_def = save_thm("word_T_def",REWRITE_RULE [GSYM n2w_def,COMP0_def] (definition "word_T_def"));
val word_0 = save_thm("word_0",REWRITE_RULE [GSYM n2w_def] (definition "word_0_def"));
val word_1 = save_thm("word_1",REWRITE_RULE [GSYM n2w_def,AONE_def] (definition "word_1_def"));
val word_T = save_thm("word_T",REWRITE_RULE [ONE_COMP_def,MOD_WL_THM,BITS_ZERO2,SUB_0] word_T_def);

val [WORD_ADD, WORD_ADD_0, WORD_ADD1, WORD_ADD_ASSOC, WORD_ADD_CLAUSES,
     WORD_ADD_COMM, WORD_ADD_INV_0_EQ, WORD_EQ_ADD_LCANCEL, WORD_EQ_ADD_RCANCEL,
     WORD_LEFT_ADD_DISTRIB, WORD_MULT_ASSOC, WORD_MULT_COMM, WORD_MULT_CLAUSES,
     MOD_WL_ELIM, WORD_ADD_RINV, WORD_NEG, WORD_NEG_1,
     WORD_OR_ASSOC, WORD_OR_COMM, WORD_OR_IDEM, WORD_OR_ABSORB, WORD_OR_COMP,
     WORD_AND_ASSOC, WORD_AND_COMM, WORD_AND_IDEM, WORD_AND_ABSORB,
     WORD_EOR_ASSOC, WORD_EOR_COMM, WORD_EOR_AND_OR,WORD_EOR_ID, WORD_EOR_INV,  WORD_AND_COMP,
     WORD_NOT_NOT, WORD_RIGHT_AND_OVER_OR, WORD_RIGHT_OR_OVER_AND, WORD_DE_MORGAN_THM] =
   map (REWRITE_RULE [word_0,word_1]) word_thms;

val _ = save_thm("WORD_ADD",WORD_ADD);
val _ = save_thm("WORD_ADD_0",WORD_ADD_0);
val _ = save_thm("WORD_ADD1",WORD_ADD1);
val _ = save_thm("WORD_ADD_ASSOC",WORD_ADD_ASSOC);
val _ = save_thm("WORD_ADD_CLAUSES",WORD_ADD_CLAUSES);
val _ = save_thm("WORD_ADD_COMM",WORD_ADD_COMM);
val _ = save_thm("WORD_ADD_INV_0_EQ",WORD_ADD_INV_0_EQ);
val _ = save_thm("WORD_EQ_ADD_LCANCEL",WORD_EQ_ADD_LCANCEL);
val _ = save_thm("WORD_EQ_ADD_RCANCEL",WORD_EQ_ADD_RCANCEL);
val _ = save_thm("WORD_LEFT_ADD_DISTRIB",WORD_LEFT_ADD_DISTRIB);
val _ = save_thm("WORD_MULT_ASSOC",WORD_MULT_ASSOC);
val _ = save_thm("WORD_MULT_COMM",WORD_MULT_COMM);
val _ = save_thm("WORD_MULT_CLAUSES",WORD_MULT_CLAUSES);
val _ = save_thm("WORD_NEG",WORD_NEG);
val _ = save_thm("WORD_NEG_1",WORD_NEG_1);
val _ = save_thm("WORD_OR_ASSOC",WORD_OR_ASSOC);
val _ = save_thm("WORD_OR_COMM",WORD_OR_COMM);
val _ = save_thm("WORD_OR_IDEM",WORD_OR_IDEM);
val _ = save_thm("WORD_OR_ABSORB",WORD_OR_ABSORB);
val _ = save_thm("WORD_OR_COMP",WORD_OR_COMP);
val _ = save_thm("WORD_AND_ASSOC",WORD_AND_ASSOC);
val _ = save_thm("WORD_AND_COMM",WORD_AND_COMM);
val _ = save_thm("WORD_AND_IDEM",WORD_AND_IDEM);
val _ = save_thm("WORD_AND_ABSORB",WORD_AND_ABSORB);
val _ = save_thm("WORD_AND_COMP",WORD_AND_COMP);
val _ = save_thm("WORD_EOR_ASSOC",WORD_EOR_ASSOC);
val _ = save_thm("WORD_EOR_COMM",WORD_EOR_COMM);
val _ = save_thm("WORD_EOR_AND_OR",WORD_EOR_AND_OR);
val _ = save_thm("WORD_EOR_ID",WORD_EOR_ID);
val _ = save_thm("WORD_EOR_INV",WORD_EOR_INV);
val _ = save_thm("WORD_NOT_NOT",WORD_NOT_NOT);
val _ = save_thm("WORD_RIGHT_AND_OVER_OR",WORD_RIGHT_AND_OVER_OR);
val _ = save_thm("WORD_RIGHT_OR_OVER_AND",WORD_RIGHT_OR_OVER_AND);
val _ = save_thm("WORD_DE_MORGAN_THM",WORD_DE_MORGAN_THM);

val WORD_ADD_RINV = save_thm("WORD_ADD_RINV",REWRITE_RULE [MOD_WL_ELIM] WORD_ADD_RINV);
val WORD_ADD_LINV = save_thm("WORD_ADD_LINV",ONCE_REWRITE_RULE [WORD_ADD_COMM] WORD_ADD_RINV);

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

val rotl_def = Def "rotl_def" `rotl x n =  x #>> (WL - n MOD WL)`;
val _ = overload_on ("#<<",Term`$rotl`);
val _ = set_fixity "#<<" (Infixl 680);


val WORD_BIT_def   = Def "WORD_BIT_def"
                         `WORD_BIT b n = BIT b (w2n n)`;
val WORD_BITS_def  = Def "WORD_BITS_def"
                         `WORD_BITS h l n = BITS h l (w2n n)`;
val WORD_SLICE_def = Def "WORD_SLICE_def"
                         `WORD_SLICE h l n = SLICE h l (w2n n)`;

(* -------------------------------------------------------- *)

val ssd = SSFRAG {ac = [(SPEC_ALL WORD_ADD_ASSOC, SPEC_ALL WORD_ADD_COMM)],
                  congs = [], convs = [], dprocs = [], filter = NONE,
                  rewrs = []};

val word_ss = bool_ss++ssd;

val WORD_RIGHT_ADD_DISTRIB = store_thm("WORD_RIGHT_ADD_DISTRIB",
  `!a b c. (a + b) * c = a * c + b * c`,
  ONCE_REWRITE_TAC [WORD_MULT_COMM]
    THEN REWRITE_TAC [WORD_LEFT_ADD_DISTRIB]
);

val WORD_NEG_ADD = store_thm("WORD_NEG_ADD",
  `!a b. ~(a + b) = ~a + ~b`,
  let val rearrange = SIMP_PROVE word_ss [] (Term`~a + a + (~b + b) = ~a + ~b + (a + b)`) in
   REPEAT STRIP_TAC
     THEN `~a + a + (~b + b) = 0w`
       by REWRITE_TAC [WORD_ADD_LINV,WORD_ADD_CLAUSES]
     THEN RULE_ASSUM_TAC (REWRITE_RULE [rearrange])
     THEN ASSUME_TAC (SYM (SPEC `a + b` WORD_ADD_LINV))
     THEN B_FULL_SIMP_TAC [WORD_EQ_ADD_RCANCEL]
  end
);

val WORD_NEG_NEG = store_thm("WORD_NEG_NEG",
  `!a. word_2comp (word_2comp a) = a`,
  STRIP_TAC
    THEN `~~a + ~a = a + ~a` by SIMP_TAC word_ss [WORD_ADD_RINV]
    THEN IMP_RES_TAC WORD_EQ_ADD_RCANCEL
);

val WORD_SUB_LNEG = save_thm("WORD_SUB_LNEG",
  (REWRITE_RULE [GSYM word_sub_def] o GSYM) WORD_NEG_ADD
);

val WORD_SUB_RNEG = save_thm("WORD_SUB_RNEG",
  (GEN `a` o GEN `b` o REWRITE_RULE [WORD_NEG_NEG] o SPECL [`a`,`~b`]) word_sub_def
);

val WORD_ADD_SUB_ASSOC = store_thm("WORD_ADD_SUB_ASSOC",
  `!a b c. a + b - c = a + (b - c)`,
  RW_TAC word_ss [word_sub_def]
);

val WORD_ADD_SUB_SYM = store_thm("WORD_ADD_SUB_SYM",
  `!a b c. a + b - c = a - c + b`,
  RW_TAC word_ss [word_sub_def]
);

val WORD_SUB_REFL = store_thm("WORD_SUB_REFL",
  `!a. a - a = 0w`,
  B_RW_TAC [word_sub_def,WORD_ADD_RINV]
);

val WORD_SUB_ADD2 = store_thm("WORD_SUB_ADD2",
  `!a b c. a + (b - a) = b`,
  REWRITE_TAC [GSYM WORD_ADD_SUB_ASSOC,WORD_ADD_SUB_SYM,WORD_SUB_REFL,WORD_ADD]
);

val WORD_ADD_SUB = store_thm("WORD_ADD_SUB",
  `!a b. a + b - b = a`,
  B_RW_TAC [WORD_ADD_SUB_ASSOC,WORD_SUB_REFL,WORD_ADD_0]
);

val WORD_SUB_ADD = save_thm("WORD_SUB_ADD",REWRITE_RULE [WORD_ADD_SUB_SYM] WORD_ADD_SUB);

val WORD_SUB_SUB = store_thm("WORD_SUB_SUB",
  `!a b c. a - (b - c) = a + c - b`,
  RW_TAC word_ss [word_sub_def,WORD_NEG_ADD,WORD_NEG_NEG]
);

val WORD_SUB_SUB2 = save_thm("WORD_SUB_SUB2",
 (GEN `a` o GEN `b` o REWRITE_RULE [WORD_ADD_SUB_SYM,WORD_SUB_REFL,WORD_ADD] o
  SPECL [`a`,`a`,`b`]) WORD_SUB_SUB
);

val WORD_NOT = store_thm("WORD_NOT",
  `!a. NOT a = ~a - 1w`,
  B_RW_TAC [WORD_NEG,WORD_ADD_SUB]
);

val WORD_SUB_LEFT_SUC = store_thm("WORD_SUB_LEFT_SUC",
  `!m n. word_suc m - n = word_suc (m - n)`,
  B_RW_TAC [WORD_ADD1,WORD_ADD_SUB_SYM]
);

val WORD_ADD_EQ_SUB = store_thm("WORD_ADD_EQ_SUB",
  `!m n p. (m + n = p) = (m = p - n)`,
  REPEAT STRIP_TAC THEN EQ_TAC
    THEN B_RW_TAC [WORD_SUB_ADD]
    THEN REWRITE_TAC [WORD_ADD_SUB]
);

val WORD_EQ_SUB_LADD = store_thm("WORD_EQ_SUB_LADD",
  `!a b c. (a = b - c) = (a + c = b)`,
  REPEAT STRIP_TAC THEN EQ_TAC
    THEN RW_TAC bool_ss [word_sub_def]
    THEN REWRITE_TAC [GSYM WORD_ADD_ASSOC,WORD_ADD_LINV,WORD_ADD_RINV,WORD_ADD_CLAUSES]
);

val WORD_EQ_SUB_RADD = store_thm("WORD_EQ_SUB_RADD",
  `!a b c. (a - b = c) = (a = c + b)`,
  REPEAT STRIP_TAC THEN EQ_TAC
    THEN RW_TAC bool_ss [word_sub_def]
    THEN REWRITE_TAC [GSYM WORD_ADD_ASSOC,WORD_ADD_LINV,WORD_ADD_RINV,WORD_ADD_CLAUSES]
);

val WORD_LCANCEL_SUB = store_thm("WORD_LCANCEL_SUB",
  `!m n p. (n - p = m - p) = (n = m)`,
  REPEAT STRIP_TAC THEN EQ_TAC
    THEN B_RW_TAC [GSYM WORD_ADD_EQ_SUB,WORD_ADD_SUB,WORD_SUB_ADD]
);

val WORD_RCANCEL_SUB = store_thm("WORD_RCANCEL_SUB",
  `!m n p. (p - n = p - m) = (n = m)`,
  REPEAT STRIP_TAC THEN EQ_TAC
    THEN B_RW_TAC [GSYM WORD_ADD_EQ_SUB,GSYM WORD_ADD_SUB_SYM,WORD_ADD_SUB,WORD_SUB_ADD]
    THEN FULL_SIMP_TAC bool_ss [GSYM WORD_ADD_EQ_SUB,WORD_EQ_SUB_RADD,WORD_EQ_ADD_LCANCEL]
);

val WORD_SUB_PLUS = store_thm("WORD_SUB_PLUS",
  `!a b c. a - (b + c) = a - b - c`,
  RW_TAC word_ss [word_sub_def,WORD_NEG_ADD]
);

val WORD_SUB_LZERO = store_thm("WORD_SUB_LZERO",
  `!a. 0w - a = ~a`,
  REWRITE_TAC [word_sub_def,WORD_ADD]
);

val WORD_NEG_0 = save_thm("WORD_NEG_0",
  (GEN_ALL o SYM o REWRITE_RULE [WORD_SUB_REFL] o SPEC `0w`) WORD_SUB_LZERO
);

val WORD_SUB_RZERO = store_thm("WORD_SUB_RZERO",
  `!a. a - 0w = a`,
  REWRITE_TAC [word_sub_def,WORD_NEG_0,WORD_ADD_0]
);

val WORD_ADD_LID_UNIQ = save_thm("WORD_ADD_LID_UNIQ",
  (GEN `a` o GEN `b` o REWRITE_RULE [WORD_SUB_REFL] o SPECL [`a`,`b`,`b`]) WORD_ADD_EQ_SUB
);

val WORD_ADD_RID_UNIQ = save_thm("WORD_ADD_RID_UNIQ",
  (GEN `a` o GEN `b` o ONCE_REWRITE_RULE [WORD_ADD_COMM] o SPECL [`b`,`a`]) WORD_ADD_LID_UNIQ
);

val WORD_ADD_SUB2 = save_thm("WORD_ADD_SUB2",ONCE_REWRITE_RULE [WORD_ADD_COMM] WORD_ADD_SUB);

val WORD_ADD_SUB3 = save_thm("WORD_ADD_SUB3",
  (GEN_ALL o REWRITE_RULE [WORD_SUB_REFL,WORD_SUB_LZERO] o SPECL [`a`,`a`]) WORD_SUB_PLUS
);

val WORD_SUB_SUB3 = save_thm("WORD_SUB_SUB3",
  (REWRITE_RULE [WORD_ADD_SUB3] o ONCE_REWRITE_RULE [WORD_ADD_COMM] o
   SPECL [`a`,`b`,`a`] o GSYM) WORD_SUB_PLUS
);

val WORD_EQ_NEG = store_thm("WORD_EQ_NEG",
  `!a b. (word_2comp a = word_2comp b) = (a = b)`,
  REWRITE_TAC [GSYM WORD_SUB_LZERO,WORD_RCANCEL_SUB]
);

val WORD_NEG_EQ = save_thm("WORD_NEG_EQ",
  (REWRITE_RULE [WORD_NEG_NEG] o SPECL [`x`,`~y`]) WORD_EQ_NEG
);

val WORD_NEG_EQ_0 = save_thm("WORD_NEG_EQ_0",
  (REWRITE_RULE [WORD_NEG_0] o SPECL [`x`,`0w`]) WORD_EQ_NEG
);

val WORD_SUB = save_thm("WORD_SUB",
  (ONCE_REWRITE_RULE [WORD_ADD_COMM] o GSYM) word_sub_def
);

val WORD_SUB_NEG = save_thm("WORD_SUB_NEG",
  (GEN_ALL o REWRITE_RULE [WORD_SUB] o SPEC `~a`) WORD_SUB_RNEG
);

val WORD_NEG_SUB = save_thm("WORD_NEG_SUB",
  (REWRITE_RULE [WORD_SUB_NEG,GSYM word_sub_def] o SPECL [`a`,`~b`] o GSYM) WORD_SUB_LNEG
);

val WORD_SUB_TRIANGLE = store_thm("WORD_SUB_TRIANGLE",
  `!a b c. a - b + (b - c) = a - c`,
  REWRITE_TAC [GSYM WORD_ADD_SUB_SYM,WORD_ADD_SUB_ASSOC,WORD_SUB_SUB3]
    THEN REWRITE_TAC [word_sub_def]
);

val WORD_NOT_0 = save_thm("WORD_NOT_0",
  (GEN_ALL o REWRITE_RULE [WORD_NEG_1,WORD_NEG_0,WORD_SUB_LZERO] o SPEC `0w`) WORD_NOT
);

val WORD_NOT_T = store_thm("WORD_NOT_T",
  `NOT word_T = 0w`,
  PROVE_TAC [WORD_NOT_0,WORD_NOT_NOT]
);

val WORD_NEG_T = store_thm("WORD_NEG_T",
  `~word_T = 1w`,
  PROVE_TAC [WORD_NEG_1,WORD_NEG_NEG]
);

(* -------------------------------------------------------- *)

val word_nchotomy = store_thm("word_nchotomy",
  `!w. ?n. w = n2w n`,
  PROVE_TAC [n2w_def,word_abs_fn_onto]
);


(*---------------------------------------------------------------------------*)
(* Support for case analysis and termination proofs of recursive definitions *)
(*---------------------------------------------------------------------------*)

val w2n_tm = prim_mk_const{Name="w2n",Thy=thyname};

val word_tyinfo =
  TypeBasePure.mk_nondatatype_info
       (word_type,
        {nchotomy = SOME word_nchotomy,
         size = SOME (w2n_tm,CONJUNCT1(SPEC_ALL boolTheory.AND_CLAUSES)),
         encode=NONE});

val _ = TypeBase.write [word_tyinfo];

(*---------------------------------------------------------------------------*)
(* Alternative way to do case analysis                                       *)
(*---------------------------------------------------------------------------*)

val FORALL_WORD = store_thm("FORALL_WORD",
`(!w. P w) = !n. P (n2w n)`,
 EQ_TAC THEN RW_TAC std_ss [] THEN
  STRIP_ASSUME_TAC (SPEC_ALL word_nchotomy) THEN RW_TAC std_ss []);

val EQUIV_EXISTS = prove(`!y. ?x. $== y = $== x`, PROVE_TAC []);

(* -------------------------------------------------------- *)

val MOD_WL_ELIM = store_thm("MOD_WL_ELIM",
  `!n. n2w (MOD_WL n) = n2w n`,
  B_RW_TAC [n2w_def,mk_word_one_one]
    THEN REWRITE_TAC [MOD_WL_QT]
);

val w2n_EVAL = store_thm("w2n_EVAL",
  `!n. w2n (n2w n) = MOD_WL n`,
  B_RW_TAC [w2n_def,n2w_def]
    THEN REWRITE_TAC [GSYM EQUIV_def, word_QUOTIENT]
);

fun Cases_on_word tm = STRUCT_CASES_TAC (SPEC tm word_nchotomy);

val w2n_ELIM = store_thm("w2n_ELIM",
  `!a. n2w (w2n a) = a`,
  REPEAT STRIP_TAC
    THEN Cases_on_word `a`
    THEN REWRITE_TAC [w2n_EVAL,MOD_WL_ELIM]
);

val n2w_11 = store_thm("n2w_11",
  `!a b. (n2w a = n2w b) = (MOD_WL a = MOD_WL b)`,
  REPEAT GEN_TAC
    THEN REWRITE_TAC [n2w_def,mk_word_one_one,GSYM EQUIV_def]
);

val w2n_n2w = store_thm("w2n_n2w",
  `!a n. (w2n a = n) ==> (a = n2w (MOD_WL n))`,
  NTAC 2 STRIP_TAC
    THEN Cases_on_word `a`
    THEN RW_TAC bool_ss [n2w_11,w2n_EVAL]
    THEN REWRITE_TAC [MOD_WL_IDEM2]
);

val w2n_11 = store_thm("w2n_11",
  `!a b. (w2n a = w2n b) = (a = b)`,
  REPEAT STRIP_TAC
    THEN Cases_on_word `a`
    THEN Cases_on_word `b`
    THEN REWRITE_TAC [w2n_EVAL,n2w_11]
);

val w2n_LT = store_thm("w2n_LT",
  `!a. w2n a < 2 EXP WL`,
  STRIP_TAC THEN Cases_on_word `a`
    THEN SIMP_TAC bool_ss [w2n_EVAL,REWRITE_RULE [LT_WL_def] LT_WL_MOD_WL]
);

(* -------------------------------------------------------- *)

fun QUOTIENT_WORD_TAC th1 th2 =
  B_SIMP_TAC [n2w_def,th1,mk_word_one_one]
    THEN REPEAT STRIP_TAC
    THEN ASM_B_SIMP_TAC [th2,word_QUOTIENT];

val ADD_EVAL = store_thm("ADD_EVAL",
  `!a b. n2w a + n2w b = n2w (a + b)`,
  QUOTIENT_WORD_TAC word_add_def ADD_WELLDEF);

val MUL_EVAL = store_thm("MUL_EVAL",
  `!a b. n2w a * n2w b = n2w (a * b)`,
  QUOTIENT_WORD_TAC word_mul_def MUL_WELLDEF);

val ONE_COMP_EVAL = store_thm("ONE_COMP_EVAL",
  `!a. NOT (n2w a) = n2w (ONE_COMP a)`,
  QUOTIENT_WORD_TAC word_1comp_def ONE_COMP_WELLDEF);

val TWO_COMP_EVAL = store_thm("TWO_COMP_EVAL",
  `!a. ~(n2w a) = n2w (TWO_COMP a)`,
  QUOTIENT_WORD_TAC word_2comp_def TWO_COMP_WELLDEF);

val WORD_SUB_LT_EQ = store_thm("WORD_SUB_LT_EQ",
  `!a b. b <= a /\ LT_WL b ==> (n2w a - n2w b = n2w (a - b))`,
  RW_TAC bool_ss [word_sub_def,TWO_COMP_EVAL,TWO_COMP_def,ADD_EVAL,SUB_LEFT_ADD,MOD_WL_IDEM]
    THEN FULL_SIMP_TAC arith_ss [LT_WL_def,n2w_11]
    THEN ONCE_REWRITE_TAC [ADD_COMM]
    THEN ASM_SIMP_TAC bool_ss [LESS_EQ_ADD_SUB]
    THEN ONCE_REWRITE_TAC [MOD_ADD]
    THEN REWRITE_TAC [MOD_WL_IDEM2,ADD,
           SIMP_CONV bool_ss [ZERO_LT_TWOEXP,DIVMOD_ID,MOD_WL_def] (Term `MOD_WL (2 ** WL)`)]
);

val LSR_ONE_EVAL = store_thm("LSR_ONE_EVAL",
  `!a. word_lsr1 (n2w a) = n2w (LSR_ONE a)`,
  QUOTIENT_WORD_TAC word_lsr1_def LSR_ONE_WELLDEF);

val ASR_ONE_EVAL = store_thm("ASR_ONE_EVAL",
  `!a. word_asr1 (n2w a) = n2w (ASR_ONE a)`,
  QUOTIENT_WORD_TAC word_asr1_def ASR_ONE_WELLDEF
);

val ROR_ONE_EVAL = store_thm("ROR_ONE_EVAL",
  `!a. word_ror1 (n2w a) = n2w (ROR_ONE a)`,
  QUOTIENT_WORD_TAC word_ror1_def ROR_ONE_WELLDEF
);

val RRX_EVAL = store_thm("RRX_EVAL",
  `!a c. RRX c (n2w a) = n2w (RRXn c a)`,
  QUOTIENT_WORD_TAC RRX_def RRX_WELLDEF
);

val LSB_EVAL = store_thm("LSB_EVAL",
  `!a. LSB (n2w a) = LSBn a`,
  QUOTIENT_WORD_TAC LSB_def LSB_WELLDEF
);

val MSB_EVAL = store_thm("MSB_EVAL",
  `!a. MSB (n2w a) = MSBn a`,
  QUOTIENT_WORD_TAC MSB_def MSB_WELLDEF
);

val OR_EVAL = store_thm("OR_EVAL",
  `!a b. (n2w a | n2w b) = n2w (OR a b)`,
  QUOTIENT_WORD_TAC bitwise_or_def OR_WELLDEF
);

val EOR_EVAL = store_thm("EOR_EVAL",
  `!a b. n2w a # n2w b = n2w (EOR a b)`,
  QUOTIENT_WORD_TAC bitwise_eor_def EOR_WELLDEF
);

val AND_EVAL = store_thm("AND_EVAL",
  `!a b. n2w a & n2w b = n2w (AND a b)`,
  QUOTIENT_WORD_TAC bitwise_and_def AND_WELLDEF
);

val BITS_EVAL = store_thm("BITS_EVAL",
  `!h l a. WORD_BITS h l (n2w a) = BITS h l (MOD_WL a)`,
  B_RW_TAC [WORD_BITS_def,w2n_EVAL]
);

val BIT_EVAL = store_thm("BIT_EVAL",
  `!b a. WORD_BIT b (n2w a) = BIT b (MOD_WL a)`,
  B_RW_TAC [WORD_BIT_def,w2n_EVAL]
);

val SLICE_EVAL = store_thm("SLICE_EVAL",
  `!h l a. WORD_SLICE h l (n2w a) = SLICE h l (MOD_WL a)`,
  B_RW_TAC [WORD_SLICE_def,w2n_EVAL]
);

val WORD_BIT_BOOLOPS = store_thm("WORD_BIT_BOOLOPS",
  `(!a b n. n < WL ==> (WORD_BIT n (a | b) = WORD_BIT n a \/ WORD_BIT n b)) /\
   (!a b n. n < WL ==> (WORD_BIT n (a & b) = WORD_BIT n a /\ WORD_BIT n b)) /\
   (!a b n. n < WL ==> (WORD_BIT n (a # b) = ~(WORD_BIT n a = WORD_BIT n b))) /\
   (!a n. n < WL ==> (WORD_BIT n (NOT a) = ~WORD_BIT n a))`,
  RW_TAC std_ss []
    THEN STRUCT_CASES_TAC (SPEC `a` word_nchotomy)
    THEN STRUCT_CASES_TAC (SPEC `b` word_nchotomy)
    THEN FULL_SIMP_TAC arith_ss [OR_EVAL,AND_EVAL,EOR_EVAL,ONE_COMP_EVAL,BIT_OF_BITS_THM,WL_def,
           OR_def,AND_def,EOR_def,ONE_COMP_BITWISE_THM,WORD_BIT_def,w2n_EVAL,n2w_11,MOD_WL_THM,
           BITWISE_THM]
);

val WORD_EQ = store_thm("WORD_EQ",
  `!w1 w2. (!x. x < WL ==> (WORD_BIT x w1 = WORD_BIT x w2)) = (w1 = w2)`,
  NTAC 2 STRIP_TAC
    THEN STRUCT_CASES_TAC (SPEC `w1` word_nchotomy)
    THEN STRUCT_CASES_TAC (SPEC `w2` word_nchotomy)
    THEN SIMP_TAC arith_ss [ADD1,BIT_OF_BITS_THM,WL_def,WORD_BIT_def,
           w2n_EVAL,n2w_11,MOD_WL_THM,DECIDE (Term `a < b + 1 = a <= b`),
           (GSYM o SIMP_RULE arith_ss [] o SPECL [`HB`,`0`]) BIT_BITS_THM]
);

(* -------------------------------------------------------- *)

val WORD_MULT_SUC = prove(
  `!a b. a * n2w (b + 1) = a * n2w b + a`,
  REPEAT STRIP_TAC
    THEN Cases_on_word `a`
    THEN SIMP_TAC arith_ss [MUL_EVAL,ADD_EVAL,LEFT_ADD_DISTRIB]
);

val WORD_NEG_LMUL = store_thm("WORD_NEG_LMUL",
  `!a b. ~(a * b) = ~a * b`,
  REPEAT STRIP_TAC THEN Cases_on_word `b`
    THEN Induct_on `n` THEN1 SIMP_TAC std_ss [WORD_MULT_CLAUSES,WORD_NEG_0]
    THEN ASM_SIMP_TAC std_ss [WORD_NEG_ADD,ADD1,GSYM MUL_EVAL,WORD_MULT_SUC]
);

val WORD_NEG_RMUL = save_thm("WORD_NEG_RMUL",
  (GEN_ALL o ONCE_REWRITE_RULE [WORD_MULT_COMM] o SPECL [`b`,`a`]) WORD_NEG_LMUL);

val WORD_RIGHT_SUB_DISTRIB = store_thm("WORD_RIGHT_SUB_DISTRIB",
  `!m n p. (m - n) * p = m * p - n * p`,
  SIMP_TAC std_ss [word_sub_def,WORD_RIGHT_ADD_DISTRIB,WORD_NEG_LMUL]
);

val WORD_LEFT_SUB_DISTRIB = save_thm("WORD_LEFT_SUB_DISTRIB",
  ONCE_REWRITE_RULE [WORD_MULT_COMM] WORD_RIGHT_SUB_DISTRIB);

(* -------------------------------------------------------- *)

val WORD_DOUBLE = store_thm("WORD_DOUBLE",
  `!a. a + a = a << 1`,
  STRIP_TAC
    THEN Cases_on_word `a`
    THEN REWRITE_TAC [ADD_EVAL,MUL_EVAL,EXP_1,word_lsl_def]
    THEN PROVE_TAC [TIMES2,MULT_COMM]
);

(* -------------------------------------------------------- *)

val FUNPOW_COMP = prove(
  `!f m n a. FUNPOW f m (FUNPOW f n a) = FUNPOW f (m + n) a`,
  Induct_on `n` THEN ASM_REWRITE_TAC [ADD_CLAUSES,FUNPOW]
);

val LSL_ADD = store_thm("LSL_ADD",
  `!a m n. a << m << n = a << (m + n)`,
  B_RW_TAC [word_lsl_def,EXP_ADD,GSYM WORD_MULT_ASSOC,MUL_EVAL]
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
  ONCE_REWRITE_TAC [GSYM MOD_WL_ELIM]
    THEN B_SIMP_TAC [MOD_WL_def,MOD_TIMES,ZERO_LT_TWOEXP]
);

val LSL_LIMIT = store_thm("LSL_LIMIT",
  `!w n.  HB < n ==> (w << n = 0w)`,
  B_RW_TAC [word_lsl_def]
    THEN IMP_RES_TAC LESS_ADD_1
    THEN RULE_ASSUM_TAC (REWRITE_RULE [GSYM ADD1,GSYM WL_def] o SIMP_RULE arith_ss [])
    THEN ASM_A_SIMP_TAC [(REWRITE_RULE [ADD_0] o SPECL [`2 EXP p`,`0`]) n2w_TIMES,
                         EXP_ADD,WORD_MULT_CLAUSES]
);

val LSL_EVAL = store_thm("LSL_EVAL",
  `!w n. w << n = if HB < n then 0w else w * n2w (2 ** n)`,
  RW_TAC bool_ss [LSL_LIMIT] THEN REWRITE_TAC [word_lsl_def]
);

(* -------------------------------------------------------- *)

val MOD_MOD_DIV = prove(
  `!a b. LT_WL (MOD_WL a DIV 2 EXP b)`,
  A_RW_TAC [MOD_WL_THM,BITS_DIV_THM]
    THEN ASSUME_TAC (SPECL [`HB`,`b`,`a`] BITSLT_THM)
    THEN ASSUME_TAC (SPECL [`SUC HB`,`b`] EXP_SUB_LESS_EQ)
    THEN IMP_RES_TAC LESS_LESS_EQ_TRANS
    THEN ASM_REWRITE_TAC [WL_def,LT_WL_def]
);

val MOD_MOD_DIV_2EXP = prove(
  `!a n. MOD_WL (MOD_WL a DIV 2 EXP n) DIV 2 = MOD_WL a DIV 2 EXP SUC n`,
  A_RW_TAC [ZERO_LT_TWOEXP,DIV_DIV_DIV_MULT,MOD_WL_IDEM,MOD_MOD_DIV,
            GSYM (ONCE_REWRITE_RULE [MULT_COMM] EXP)]
);

val LSR_EVAL = store_thm("LSR_EVAL",
  `!n. (n2w a) >>> n = n2w (MOD_WL a DIV 2 EXP n)`,
  Induct_on `n` THEN1 B_SIMP_TAC [FUNPOW,word_lsr_def,EXP,DIV_1,MOD_WL_ELIM]
    THEN B_FULL_SIMP_TAC [word_lsr_def,FUNPOW_SUC,LSR_ONE_EVAL,LSR_ONE_def,MOD_MOD_DIV_2EXP]
);

val LSR_THM = store_thm("LSR_THM",
  `!x n. (n2w n) >>> x = n2w (BITS HB (MIN WL x) n)`,
  A_RW_TAC [LSR_EVAL,MOD_WL_THM,BITS_DIV_THM,MIN_DEF,WL_def,BITS_ZERO]
);

val LSR_LIMIT = store_thm("LSR_LIMIT",
  `!x w. HB < x ==> (w >>> x = 0w)`,
  REPEAT STRIP_TAC
    THEN Cases_on_word `w`
    THEN A_RW_TAC [LSR_THM,MIN_DEF,WL_def,BITS_ZERO]
);

(* -------------------------------------------------------- *)

val MOD_WL = (GEN_ALL o CONJUNCT2 o SPEC_ALL o REWRITE_RULE [WL_POS] o SPEC `WL`) DIVISION;

val n2w_TIMES2 = ONCE_REWRITE_RULE [ADD_COMM] n2w_TIMES;

val LEFT_SHIFT_LESS = prove(
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
  `!x n. 0 < x MOD WL ==> LT_WL (BITS HB (x MOD WL) n + BITS (x MOD WL - 1) 0 n * 2 EXP (WL - x MOD WL))`,
  B_RW_TAC [LT_WL_def]
    THEN RULE_ASSUM_TAC (REWRITE_RULE [GSYM ONE,LESS_EQ])
    THEN POP_ASSUM (fn th =>
           ASSUME_TAC (SIMP_RULE arith_ss [th,ADD1,SUB_ADD] (SPECL [`x MOD WL - 1`,`0`,`n`] BITSLT_THM)))
    THEN ASSUME_TAC (REWRITE_RULE [GSYM WL_def] (SPECL [`HB`,`x MOD WL`,`n`] BITSLT_THM))
    THEN ASSUME_TAC (MATCH_MP LESS_IMP_LESS_OR_EQ (SPEC `x` MOD_WL))
    THEN ASM_B_SIMP_TAC [lem3]
);

val lem5 = prove(
  `!x n. MOD_WL (BITS HB (x MOD WL) n + BITS (x MOD WL - 1) 0 n * 2 EXP (WL - x MOD WL)) =
          if x MOD WL = 0 then BITS HB 0 n
                          else BITS HB (x MOD WL) n + BITS (x MOD WL - 1) 0 n * 2 EXP (WL - x MOD WL)`,
  B_RW_TAC [] THEN1 A_SIMP_TAC [MOD_TIMES,ZERO_LT_TWOEXP,MOD_MOD,MOD_WL_def,GSYM MOD_WL_THM]
    THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_ZERO_LT_ZERO])
    THEN ASM_B_SIMP_TAC [lem4,MOD_WL_IDEM]
);

val lem6 = prove(
  `!h b n. (BITS b b n MOD 2 = 1) = BIT b n`,
  A_RW_TAC [GSYM ODD_MOD2_LEM,GSYM LSB_ODD,LSBn_def,BIT_def,BITS_COMP_THM]
);

val lem7 = PROVE [MULT_COMM,MULT_ASSOC] `!(a:num) b c. a * (b * c) = (a * c) * b`;

(* |- !n l h. BITS h l n DIV 2 = BITS h (l + 1) n *)
val BITS_DIV_THM2 = (REWRITE_RULE [EXP_1] o GEN_ALL o INST [`n` |-> `1`] o SPEC_ALL) BITS_DIV_THM;

(* |- !n. BITS 0 0 n = n MOD 2 *)
val BITS00 = GEN_ALL (REWRITE_CONV [SUC_SUB,DIV_1,EXP,EXP_1,SYM TWO,BITS_THM] (Term`BITS 0 0 n`));

val SPEC_MOD_PLUS_1 = REWRITE_RULE [WL_POS] (SPEC `WL` MOD_PLUS_1);
val SPEC_MOD_ADD_1  = REWRITE_RULE [WL_POS] (SPEC `WL` MOD_ADD_1);

(* |- !n h. SLICE h 0 n = BITS h 0 n *)
val SLICE_COR = (GEN_ALL o SIMP_RULE arith_ss [] o SPECL [`n`,`h`,`0`]) SLICE_THM;

(* |- !n x. n #>> (SUC x) = word_ror1 (n #>> x) *)
val ROR_LEM = GEN_ALL (RIGHT_REWRITE_RULE [GSYM word_ror_def]
                 (SIMP_CONV bool_ss [word_ror_def,FUNPOW_SUC] (Term`n #>> (SUC x)`)));

val ROR_THM = store_thm("ROR_THM",
  `!x n. (n2w n) #>> x = let x' = x MOD WL in
                          n2w (BITS HB x' n + (BITS (x' - 1) 0 n) * 2 EXP (WL - x'))`,
  Induct_on `x`
    THEN REPEAT STRIP_TAC
    THEN1 A_SIMP_TAC [ZERO_MOD,WL_POS,word_ror_def,FUNPOW,n2w_TIMES2,SYM MOD_WL_THM,MOD_WL_ELIM]
    THEN POP_ASSUM (fn th => S_SIMP_TAC [th,ROR_LEM,ROR_ONE_EVAL,ROR_ONE_def,LSR_ONE_def])
    THEN Cases_on `(x + 1) MOD WL = 0`
    THENL [
       IMP_RES_TAC SPEC_MOD_PLUS_1
         THEN RULE_ASSUM_TAC (SIMP_RULE bool_ss [ADD_EQ_SUB,WL_GEQ_ONE,WL_SUB_ONE])
         THEN A_RW_TAC [lem5,lem6,ADD1,WL_SUB_HB,EXP_1,n2w_TIMES,n2w_TIMES2,MOD_WL_THM,
                        MOD_WL_ELIM,ADD_DIV_ADD_DIV,BITS_DIV_THM2,BITS_ZERO,
                        LSB_ODD,ODD_MOD2_LEM,MOD_TIMES]
         THENL [
           A_RW_TAC [SBIT_def,BIT_def] THEN B_FULL_SIMP_TAC [NOT_BITS2],
           IMP_RES_TAC NOT_ZERO_ADD1
             THEN ASM_B_SIMP_TAC [SUC_SUB1,SIMP_RULE arith_ss [] (SPECL [`p`,`0`] BITS_SUC)]
         ],
       IMP_RES_TAC SPEC_MOD_ADD_1
         THEN A_RW_TAC [ADD1,BITS_DIV_THM2,WL_SUB_ONE,lem5]
         THENL [
           A_SIMP_TAC [lem7,WL_def,LSB_ODD,ODD_MOD2_LEM,EXP,MOD_TIMES]
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
);

val ROR_CYCLE = store_thm("ROR_CYCLE",
  `!x w. w #>> (x * WL) = w`,
  REPEAT STRIP_TAC
    THEN Cases_on_word `w`
    THEN A_SIMP_TAC [MOD_EQ_0,WL_POS,ROR_THM,n2w_TIMES2,SYM MOD_WL_THM,MOD_WL_ELIM]
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
  B_RW_TAC [LSR_ONE_def,MOD_WL_THM,EXP,DIV_1,REWRITE_RULE [GSYM WL_def] (SPEC `HB` BITS_LT_HIGH),lem6b]
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
       ASM_A_SIMP_TAC [BITS_THM,CONJUNCT1 EXP,DIV_1]
         THEN ASM_REWRITE_TAC [GSYM BITS_THM2],
       IMP_RES_TAC NOT_ZERO_ADD1
         THEN ASM_A_SIMP_TAC [EXP,WL_def]
         THEN B_SIMP_TAC [LESS_EQ_ADD_SUB,EXP_SUB_LESS_EQ,lem6c,TIMES2,GSYM ADD_ASSOC,DIV_MULT_1]
    ]
);

val lem10 = prove(
  `!a b. 2 EXP a <= 2 EXP (a - b) ==> (a = 0) \/ (b = 0)`,
  SRW_TAC [ARITH_ss][]
);

val lem11 = (GEN_ALL o REWRITE_RULE [EXP,GSYM NOT_LESS_EQUAL])
              (MATCH_MP TWOEXP_MONO (DECIDE (Term `h < SUC h`)));

val TWOEXP_LT_EQ1 = prove(
  `!n. 2 EXP n <= 1 ==> (2 EXP n = 1)`,
  REPEAT STRIP_TAC THEN ASSUME_TAC (SPEC `n` ZERO_LT_TWOEXP) THEN DECIDE_TAC
);

(* |- !n x. n >> (SUC x) = word_asr1 (n >> x) *)
val ASR_LEM = GEN_ALL (RIGHT_REWRITE_RULE [GSYM word_asr_def]
                 (REWRITE_CONV [word_asr_def,FUNPOW_SUC] (Term`n >> (SUC x)`)));

val ASR_THM = store_thm("ASR_THM",
  `!x n. (n2w n) >> x =
           let x' = MIN HB x in
           let s = BITS HB x' n in
             n2w (if MSBn n then 2 EXP WL - 2 EXP (WL - x') + s else s)`,
  Induct_on `x`
    THEN REPEAT STRIP_TAC THEN1 A_SIMP_TAC [word_asr_def,FUNPOW,MIN_DEF,SYM MOD_WL_THM,MOD_WL_ELIM]
    THEN POP_ASSUM (fn th => S_RW_TAC [th,REDUCE_RULE (SPEC `F` SBIT_def),lem3,lem7,
                             lem,lem2,MIN_DEF,ASR_LEM,ASR_ONE_EVAL,ASR_ONE_def])
    THEN A_FULL_SIMP_TAC [BITS_ZERO,lem9,SBIT_def]
    THEN ASM_A_SIMP_TAC [lem8c,lem4,BITS_ZERO,WL_SUB_HB,WL_SUB_SUC_X]
    THENL [
       A_RW_TAC [WL_def,SUB_RIGHT_ADD,EXP,EXP_1,TWOEXP_LT_EQ1],
       `x = HB` by DECIDE_TAC
         THEN A_RW_TAC [WL_def,SUB_RIGHT_ADD,EXP,EXP_1,TWOEXP_LT_EQ1],
       `HB - x <= HB` by DECIDE_TAC THEN
       `2 ** (HB - x) <= 2 ** HB` by SRW_TAC [][] THEN
       SRW_TAC [ARITH_ss]
               [DECIDE (Term`!m n p. n <= m ==> (m - n + p = m + p - n)`),
                WL_def, EXP]
    ]
);

val MIN_LEM = prove(
  `!a b. a <= b ==> (MIN a b = a)`,
  A_RW_TAC [MIN_DEF]
);

val ASR_LIMIT = store_thm("ASR_LIMIT",
  `!x w. HB <= x ==> (w >> x = if MSB w then word_T else 0w)`,
  REPEAT STRIP_TAC
    THEN Cases_on_word `w`
    THEN A_RW_TAC [ASR_THM,MSB_EVAL,MSBn_def,BIT_def,MIN_LEM,NOT_BITS2,
                   WL_SUB_HB,SUB_RIGHT_ADD,word_T]
    THEN FULL_SIMP_TAC (srw_ss()) [WL_def]
    THEN `HB = 0` by DECIDE_TAC
    THEN SRW_TAC [][]
);

(* -------------------------------------------------------- *)

val ZERO_SHIFT = store_thm("ZERO_SHIFT",
  `(!n. 0w << n = 0w) /\ (!n. 0w >> n = 0w) /\
   (!n. 0w >>> n = 0w) /\ (!n. 0w #>> n = 0w)`,
  A_RW_TAC [MUL_EVAL,word_lsl_def,ASR_THM,BITS_ZERO2,MSBn_def,BIT_def,LSR_THM,ROR_THM]
);

val ZERO_SHIFT2 = store_thm("ZERO_SHIFT2",
  `(!a. a << 0 = a) /\ (!a. a >> 0 = a) /\
   (!a. a >>> 0 = a) /\ (!a. a #>> 0 = a)`,
  A_RW_TAC [word_lsr_def,word_asr_def,word_ror_def,word_lsl_def,FUNPOW,WORD_MULT_CLAUSES]
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
    THEN A_FULL_SIMP_TAC [EXP_ADD,EXP,ZERO_LT_TWOEXP,GSYM DIV_DIV_DIV_MULT,DIV_1,lem,lem2]
);

val lem3b = prove(
  `!m n. (2 EXP (m + n) - 1) MOD 2 EXP n = 2 EXP n - 1`,
  Induct_on `m`
    THEN STRIP_TAC THEN1 A_SIMP_TAC [LESS_MOD,ZERO_LT_TWOEXP]
    THEN B_SIMP_TAC [ADD_CLAUSES,EXP,TIMES2]
    THEN SUBST_OCCS_TAC [([1],SPECL [`m`,`n`,`2`] EXP_ADD)]
    THEN ASM_B_SIMP_TAC [MOD_TIMES,ZERO_LT_TWOEXP,LESS_EQ_ADD_SUB,
                         REWRITE_RULE [SYM ONE,LESS_EQ] ZERO_LT_TWOEXP]
);

val LSB_COMP0 = (SIMP_RULE arith_ss [WL_def,GSYM LSBn_def] o SPEC `0`) ONE_COMP_TRUE;
val MSB_COMP0 = (SIMP_RULE arith_ss [WL_def,GSYM MSBn_def] o SPEC `HB`) ONE_COMP_TRUE;

val lem4 = SIMP_RULE arith_ss [GSYM ADD1] (SPECL [`n`,`1`] lem3);
val lem5 = SIMP_RULE arith_ss [GSYM ADD1] (SPECL [`0`,`HB`] lem3b);

val ASR_word_T = store_thm("ASR_word_T",
  `!n. word_T >> n = word_T`,
  Induct_on `n` THEN1 REWRITE_TAC [ZERO_SHIFT2]
    THEN ASM_REWRITE_TAC [ASR_LEM,ASR_ONE_EVAL,word_T_def,ASR_ONE_def,
                          LSR_ONE,BITS_THM,EXP_1,SBIT_def,MSB_COMP0]
    THEN A_SIMP_TAC [ONE_COMP_def,MOD_WL_THM,BITS_ZERO2,WL_def,lem4,lem5]
    THEN REWRITE_TAC [EXP]
);

val ROR_word_T = store_thm("ROR_word_T",
  `!n. word_T #>> n = word_T`,
  Induct_on `n` THEN1 REWRITE_TAC [ZERO_SHIFT2]
    THEN ASM_REWRITE_TAC [ROR_LEM,ROR_ONE_EVAL,word_T_def,ROR_ONE_def,
                          LSR_ONE,BITS_THM,EXP_1,SBIT_def,LSB_COMP0]
    THEN A_SIMP_TAC [ONE_COMP_def,MOD_WL_THM,BITS_ZERO2,WL_def,lem4,lem5]
    THEN REWRITE_TAC [EXP]
);

val SHIFT_Inversion = Q.store_thm
  ("SHIFT_Inversion",
  `!s n. (s #>> n #<< n = s) /\ (s #<< n #>> n = s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [rotl_def,ROR_ADD] THEN
  Cases_on `n < WL` THEN
  ASM_SIMP_TAC arith_ss [(REWRITE_RULE [MULT_CLAUSES] o SPEC `1`) ROR_CYCLE] THEN
  `0 < WL` by SIMP_TAC arith_ss [WL_def] THEN IMP_RES_TAC DA THEN
  POP_ASSUM (STRIP_ASSUME_TAC o SPEC `n`) THEN
  ASM_SIMP_TAC arith_ss [ONCE_REWRITE_RULE [ADD_COMM] MOD_MULT,ROR_CYCLE,
                         (ONCE_REWRITE_RULE [MULT_COMM] o GSYM) MULT_CLAUSES]);

val lem = prove(
  `!a n. a < WL - n MOD WL ==> (a + n MOD WL = (a + n) MOD WL)`,
  RW_TAC std_ss [WL_def]
    THEN STRIP_ASSUME_TAC ((SIMP_RULE arith_ss [] o SPECL [`n`,`SUC HB`]) DA)
    THEN `n MOD SUC HB = r` by METIS_TAC [ADD_COMM,MOD_UNIQUE]
    THEN `a + r < SUC HB` by DECIDE_TAC
    THEN ASM_SIMP_TAC std_ss [LESS_MOD,DECIDE (Term `!x. 0 < SUC x`),
           ADD_ASSOC,ONCE_REWRITE_RULE [ADD_COMM] MOD_TIMES]
);

val lem2 = prove(
  `!a. a MOD WL <= HB`,
  SIMP_TAC arith_ss [DECIDE (Term `a < SUC b ==> a <= b`),WL_def,DIVISION]
);

val lem3 = prove(
  `!a b. x <= b ==> (MIN b x = x)`,
  RW_TAC arith_ss [MIN_DEF]
);

val lem5 = prove(
  `!n. ?q. WL - n MOD WL + n = q * WL`,
  STRIP_TAC
    THEN STRIP_ASSUME_TAC ((SIMP_RULE arith_ss [] o SPECL [`n`,`SUC HB`]) DA)
    THEN ASM_SIMP_TAC arith_ss [WL_def,ONCE_REWRITE_RULE [ADD_COMM] MOD_MULT,
           simpLib.SIMP_PROVE arith_ss [RIGHT_ADD_DISTRIB] (Term `!a b. (a:num) + b * a = (b + 1) * a`)]
);

val lem6 = simpLib.SIMP_PROVE arith_ss [MIN_DEF] (Term `!a b. b <= a ==> (MIN a b = b)`);

val WORD_BIT_ROR = store_thm("WORD_BIT_ROR",
  `!a n w. a < WL ==> (WORD_BIT a (w #>> n) = WORD_BIT ((a + n) MOD WL) w)`,
  REPEAT STRIP_TAC
    THEN STRUCT_CASES_TAC (SPEC `w` word_nchotomy)
    THEN `a <= HB /\ (a + n) MOD WL <= HB`
      by FULL_SIMP_TAC arith_ss [WL_def,DIVISION,DECIDE (Term `!a b. a < SUC b ==> a <= b`)]
    THEN ASM_SIMP_TAC (arith_ss++boolSimps.LET_ss)
           [ROR_THM,WORD_BIT_def,w2n_EVAL,n2w_11,MOD_WL_THM,BIT_OF_BITS_THM]
    THEN Cases_on `a < WL - n MOD WL`
    THENL [
      IMP_RES_TAC lem
        THEN IMP_RES_TAC LESS_ADD_1
        THEN POP_ASSUM (K ALL_TAC)
        THEN POP_ASSUM SUBST_ALL_TAC
        THEN REWRITE_TAC [DECIDE (Term `a + (p + 1) = p + SUC a`)]
        THEN ASM_SIMP_TAC arith_ss [lem2,lem3,EXP_ADD,BITS_SUM2,ZERO_LT_TWOEXP,BIT_def,
               MULT_ASSOC,BITS_COMP_THM2],
      RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS])
        THEN IMP_RES_TAC LESS_EQUAL_ADD
        THEN NTAC 2 (POP_ASSUM (K ALL_TAC))
        THEN ASM_SIMP_TAC std_ss  [BIT_def,GSYM BITS_DIV_THM,BITS_SUM,
               (REWRITE_RULE [GSYM WL_def] o SPECL [`HB`,`n MOD WL`]) BITSLT_THM]
        THEN SIMP_TAC std_ss [BITS_DIV_THM]
        THEN SIMP_TAC std_ss [(GSYM o ONCE_REWRITE_RULE [ADD_COMM] o REWRITE_RULE [MIN_IDEM] o
               SPECL [`p + (WL - n MOD WL)`,`WL - n MOD WL`,`p`,`p`]) BITS_COMP_THM2]
        THEN SIMP_TAC bool_ss [DECIDE (Term `(x:num) <= x + p`),BITS_ZERO4]
        THEN SIMP_TAC std_ss []
        THEN `p <= n MOD WL - 1` by DECIDE_TAC
        THEN ASM_SIMP_TAC std_ss [ADD_0,BITS_COMP_THM2,DECIDE (Term `(a:num) + b - a = b`),MIN_IDEM,lem6]
        THEN `p < WL` by DECIDE_TAC THEN STRIP_ASSUME_TAC (SPEC `n` lem5)
        THEN ONCE_REWRITE_TAC [DECIDE (Term `!a b c. (a:num) + b + c = a + c + b`)]
        THEN ASM_SIMP_TAC std_ss [MOD_MULT]
    ]
);

val WORD_BIT_LSR = store_thm("WORD_BIT_LSR",
  `!a n w. a < WL ==> (WORD_BIT a (w >>> n) = a + n < WL /\ WORD_BIT (a + n) w)`,
  REPEAT STRIP_TAC
    THEN STRUCT_CASES_TAC (SPEC `w` word_nchotomy)
    THEN Tactical.REVERSE (Cases_on `n <= WL`)
    THEN1 FULL_SIMP_TAC arith_ss [WL_def,LSR_LIMIT,WORD_BIT_def,w2n_EVAL,n2w_11,
            MOD_WL_THM,BITS_ZERO2,BIT_ZERO]
    THEN FULL_SIMP_TAC arith_ss [WL_def,LSR_THM,WORD_BIT_def,w2n_EVAL,n2w_11,MOD_WL_THM,lem6]
    THEN Cases_on `a + n < SUC HB` THEN ASM_SIMP_TAC arith_ss [BIT_OF_BITS_THM,BIT_OF_BITS_THM2]
);

val WORD_BIT_LSL = store_thm("WORD_BIT_LSL",
  `!a n w. a < WL ==> (WORD_BIT a (w << n) = n <= a /\ WORD_BIT (a - n) w)`,
  REPEAT STRIP_TAC
    THEN STRUCT_CASES_TAC (SPEC `w` word_nchotomy)
    THEN Tactical.REVERSE (Cases_on `n <= HB`)
    THEN1 FULL_SIMP_TAC arith_ss [WL_def,NOT_LESS_EQUAL,LSL_LIMIT,WORD_BIT_def,
            w2n_EVAL,n2w_11,MOD_WL_THM,BITS_ZERO2,BIT_ZERO]
    THEN FULL_SIMP_TAC arith_ss [WL_def,LSL_EVAL,MUL_EVAL,WORD_BIT_def,w2n_EVAL,
            n2w_11,MOD_WL_THM,BIT_OF_BITS_THM]
    THEN Cases_on `n <= a`
    THEN ASM_SIMP_TAC arith_ss []
    THENL [
      IMP_RES_TAC LESS_EQUAL_ADD THEN POP_ASSUM (K ALL_TAC)
        THEN ASM_SIMP_TAC arith_ss [BIT_def]
        THEN ONCE_REWRITE_TAC [ADD_COMM]
        THEN ASM_SIMP_TAC arith_ss [BITS_ZERO4,
               (GEN_ALL o GSYM o REWRITE_RULE [MIN_IDEM] o SPECL [`p + n`,`n`,`p`,`p`]) BITS_COMP_THM2]
        THEN ASM_SIMP_TAC arith_ss [BITS_COMP_THM2],
      FULL_SIMP_TAC arith_ss [NOT_LESS_EQUAL]
        THEN IMP_RES_TAC LESS_ADD THEN POP_ASSUM (SUBST_ALL_TAC o SYM)
        THEN ASM_SIMP_TAC arith_ss [BIT_def,EXP_ADD,MULT_ASSOC,BITS_ZERO3,BITS_ZERO4]
        THEN `0 < p` by DECIDE_TAC
        THEN POP_ASSUM (fn th => STRIP_ASSUME_TAC (MATCH_MP LESS_ADD_1 th))
        THEN ASM_SIMP_TAC arith_ss [EXP_ADD,MULT_ASSOC,MOD_EQ_0]
    ]
);

(* -------------------------------------------------------- *)

val ADD_EVAL2 = save_thm("ADD_EVAL2",
  GEN_ALL (GEN_REWRITE_RULE (ONCE_DEPTH_CONV o RAND_CONV) empty_rewrites [GSYM MOD_WL_ELIM] ADD_EVAL)
);

val MUL_EVAL2 = save_thm("MUL_EVAL2",
  GEN_ALL (GEN_REWRITE_RULE (ONCE_DEPTH_CONV o RAND_CONV) empty_rewrites [GSYM MOD_WL_ELIM] MUL_EVAL)
);

val LSR_ONE_EVAL2 = save_thm("LSR_ONE_EVAL2",
  GEN_ALL (REWRITE_RULE [LSR_ONE_def] LSR_ONE_EVAL)
);

val LSB_EVAL2 = save_thm("LSB_EVAL2",GEN_ALL (REWRITE_RULE [LSB_ODD] LSB_EVAL));

(* -------------------------------------------------------- *)

val WORD_BITSLT_THM = store_thm("WORD_BITSLT_THM",
  `!h l n. WORD_BITS h l n < 2 EXP (SUC h-l)`,
  B_RW_TAC [BITSLT_THM,WORD_BITS_def]
);

val WORD_BITS_COMP_THM = store_thm("WORD_BITS_COMP_THM",
  `!h1 l1 h2 l2 n. h2 + l1 <= h1 ==> (BITS h2 l2 (WORD_BITS h1 l1 n) = WORD_BITS (h2+l1) (l2+l1) n)`,
  B_RW_TAC [WORD_BITS_def,BITS_COMP_THM]
);

val WORD_BITS_COMP_THM2 = store_thm("WORD_BITS_COMP_THM2",
  `!h1 l1 h2 l2 n. BITS h2 l2 (WORD_BITS h1 l1 n) = WORD_BITS (MIN h1 (h2 + l1)) (l2 + l1) n`,
  B_RW_TAC [WORD_BITS_def,BITS_COMP_THM2]
);

val WORD_BITS_DIV_THM = store_thm("WORD_BITS_DIV_THM",
  `!h l n x. (WORD_BITS h l x) DIV 2 EXP n = WORD_BITS h (l + n) x`,
  B_RW_TAC [WORD_BITS_def,BITS_DIV_THM]
);

val WORD_BIT_THM = store_thm("WORD_BIT_THM",
  `!b n. WORD_BIT b n = (WORD_BITS b b n = 1)`,
  B_RW_TAC [WORD_BITS_def,WORD_BIT_def,BIT_def]
);

val WORD_SLICE_THM = store_thm("WORD_SLICE_THM",
  `!n h l. WORD_SLICE h l n = WORD_BITS h l n * 2 EXP l`,
  B_RW_TAC [WORD_SLICE_def,WORD_BITS_def,SLICE_THM]
);

val WORD_BITS_SLICE_THM = store_thm("WORD_BITS_SLICE_THM",
  `!h l n. BITS h l (WORD_SLICE h l n) = WORD_BITS h l n`,
  B_RW_TAC [WORD_SLICE_def,WORD_BITS_def,BITS_SLICE_THM]
);

val WORD_SLICE_ZERO_THM = store_thm("WORD_SLICE_ZERO_THM",
  `!n h. WORD_SLICE h 0 n = WORD_BITS h 0 n`,
  A_RW_TAC [WORD_SLICE_THM]
);

val WORD_SLICE_COMP_THM = store_thm("WORD_SLICE_COMP_THM",
  `!h m l a. (SUC m) <= h /\ l <= m ==> (WORD_SLICE h (SUC m) a + WORD_SLICE m l a = WORD_SLICE h l a)`,
  B_RW_TAC [WORD_SLICE_def,SLICE_COMP_THM]
);

val WORD_SLICE_COMP_RWT = store_thm("WORD_SLICE_COMP_RWT",
  `!h m' m l a. l <= m /\ (m' = m + 1) /\ m < h ==>
      (WORD_SLICE h m' a + WORD_SLICE m l a = WORD_SLICE h l a)`,
  B_RW_TAC [WORD_SLICE_def,SLICE_COMP_RWT]
);

val WORD_BITS_ZERO = store_thm("WORD_BITS_ZERO",
  `!h l n. h < l ==> (WORD_BITS h l n = 0)`,
  B_RW_TAC [WORD_BITS_def,BITS_ZERO]
);

val WORD_SLICE_ZERO = store_thm("WORD_SLICE_ZERO",
  `!h l n. h < l ==> (WORD_SLICE h l n = 0)`,
  B_RW_TAC [WORD_SLICE_def,SLICE_ZERO]
);

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val CMP_NZCV_def = Def "CMP_NZCV_def"
   `CMP_NZCV a b =
      let q = w2n a + w2n (word_2comp b) in
      let r = n2w q in
      (MSB r,
       r = 0w,
       BIT WL q \/ (b = 0w),
       ~(MSB a = MSB b) /\ ~(MSB r = MSB a))`;

val WORD_LT_def = Def "WORD_LT_def" `
  word_lt a b = let (n,z,c,v) = CMP_NZCV a b in ~(n = v)`;

val WORD_GT_def = Def "WORD_GT_def" `
  word_gt a b = let (n,z,c,v) = CMP_NZCV a b in ~z /\ (n = v)`;

val WORD_LE_def = Def "WORD_LE_def" `
  word_le a b = let (n,z,c,v) = CMP_NZCV a b in z \/ ~(n = v)`;

val WORD_GE_def = Def "WORD_GE_def"  `
  word_ge a b = let (n,z,c,v) = CMP_NZCV a b in n = v`;

val WORD_LS_def = Def "WORD_LS_def" `
  word_ls a b = let (n,z,c,v) = CMP_NZCV a b in ~c \/ z`;

val WORD_HI_def = Def "WORD_HI_def" `
  word_hi a b = let (n,z,c,v) = CMP_NZCV a b in c /\ ~z`;

val WORD_LO_def = Def "WORD_LO_def" `
  word_lo a b = let (n,z,c,v) = CMP_NZCV a b in ~c`;

val WORD_HS_def = Def "WORD_HS_def"  `
  word_hs a b = let (n,z,c,v) = CMP_NZCV a b in c`;

val EQUAL_THEN_SUB_ZERO = (GEN_ALL o REWRITE_RULE [WORD_SUB_REFL] o SPECL [`b`,`a`,`b`]) WORD_LCANCEL_SUB;

val WORD_LT = save_thm("WORD_LT",
  SIMP_RULE std_ss [CMP_NZCV_def,GSYM ADD_EVAL,w2n_ELIM,GSYM word_sub_def] WORD_LT_def);
val WORD_GT = save_thm("WORD_GT",
  SIMP_RULE std_ss [CMP_NZCV_def,EQUAL_THEN_SUB_ZERO,GSYM ADD_EVAL,w2n_ELIM,GSYM word_sub_def] WORD_GT_def);
val WORD_LE = save_thm("WORD_LE",
  SIMP_RULE std_ss [CMP_NZCV_def,EQUAL_THEN_SUB_ZERO,GSYM ADD_EVAL,w2n_ELIM,GSYM word_sub_def] WORD_LE_def);
val WORD_GE = save_thm("WORD_GE",
  SIMP_RULE std_ss [CMP_NZCV_def,GSYM ADD_EVAL,w2n_ELIM,GSYM word_sub_def] WORD_GE_def);
val WORD_LS = save_thm("WORD_LS",
  SIMP_RULE std_ss [CMP_NZCV_def,EQUAL_THEN_SUB_ZERO,GSYM ADD_EVAL,w2n_ELIM,GSYM word_sub_def] WORD_LS_def);
val WORD_HI = save_thm("WORD_HI",
  SIMP_RULE std_ss [CMP_NZCV_def,EQUAL_THEN_SUB_ZERO,GSYM ADD_EVAL,w2n_ELIM,GSYM word_sub_def] WORD_HI_def);
val WORD_LO = save_thm("WORD_LO",
  SIMP_RULE std_ss [CMP_NZCV_def,GSYM ADD_EVAL,w2n_ELIM,GSYM word_sub_def] WORD_LO_def);
val WORD_HS = save_thm("WORD_HS",
  SIMP_RULE std_ss [CMP_NZCV_def,GSYM ADD_EVAL,w2n_ELIM,GSYM word_sub_def] WORD_HS_def);

(* -------------------------------------------------------- *)

val SPEC_LESS_EXP_SUC_MONO = prove(
  `!n. 2 ** n < 2 ** SUC n`,
  SRW_TAC [][])

val SPLIT_2_EXP_WL = prove(`2 ** WL = 2 ** HB + 2 ** HB`,SIMP_TAC arith_ss [EXP,WL_def]);

val WORD_NEG_L = store_thm("WORD_NEG_L",
  `~word_L = word_L`,
  SIMP_TAC bool_ss [LESS_MOD,SPEC_LESS_EXP_SUC_MONO,word_L_def,n2w_11,
                    TWO_COMP_EVAL,TWO_COMP_def,MOD_WL_THM,BITS_ZERO3]
    THEN REWRITE_TAC [SPLIT_2_EXP_WL,ADD_SUB]
    THEN SIMP_TAC arith_ss [GSYM EXP,LESS_MOD,SPEC_LESS_EXP_SUC_MONO]
);

(* -------------------------------------------------------- *)

val lem3 = (SIMP_RULE arith_ss [] o SPECL [`HB`,`0`,`HB - 1`,`0`]) BITS_COMP_THM;

val lem8 = DECIDE (Term `!n. ~(n = 0) ==> (SUC (n - 1) = n)`);

val lem6 = prove(
  `!b n. ~(b = 0) ==>
     (SLICE b b n + SLICE (b - 1) 0 n = SLICE b 0 n)`,
   REPEAT STRIP_TAC
     THEN POP_ASSUM
          (fn th => REWRITE_TAC [(SIMP_RULE arith_ss [lem8,th] o SPECL [`b`,`b - 1`,`0`,`n`]) SLICE_COMP_THM])
);

val MSB_THM1 = prove(
  `!a. ~(HB = 0) /\ MSB a ==> (w2n a = 2 EXP HB + WORD_BITS (HB - 1) 0 a)`,
  STRIP_TAC THEN Cases_on_word `a`
    THEN RW_TAC bool_ss [MSB_EVAL,MSBn_def,w2n_EVAL,MOD_WL_THM,WORD_BITS_def,lem3]
    THEN IMP_RES_TAC BIT_SLICE_THM2
    THEN POP_ASSUM (SUBST1_TAC o SYM)
    THEN ASM_SIMP_TAC bool_ss [lem6,GSYM SLICE_ZERO_THM]
);

val MSB_THM2 = prove(
  `!a. ~(HB = 0) /\ MSB a ==> (w2n (word_2comp a) = 2 EXP HB - WORD_BITS (HB - 1) 0 a)`,
  STRIP_TAC THEN Cases_on_word `a`
    THEN REPEAT STRIP_TAC THEN IMP_RES_TAC MSB_THM1
    THEN FULL_SIMP_TAC bool_ss [MSB_EVAL,MSBn_def,w2n_EVAL,MOD_WL_THM,WORD_BITS_def,
                                TWO_COMP_EVAL,TWO_COMP_def,lem3]
    THEN ASM_SIMP_TAC arith_ss [BITS_ZERO3,GSYM ADD1,SPEC_MOD_TIMES,MOD_MOD,ZERO_LT_TWOEXP,lem8]
    THEN REWRITE_TAC [SPLIT_2_EXP_WL,SUB_PLUS,ADD_SUB]
    THEN ASSUME_TAC (SPEC `HB` SPEC_LESS_EXP_SUC_MONO)
    THEN `2 EXP HB - n MOD 2 EXP HB <= 2 EXP HB` by DECIDE_TAC
    THEN IMP_RES_TAC LESS_EQ_LESS_TRANS
    THEN ASM_SIMP_TAC bool_ss [ZERO_LT_TWOEXP,LESS_MOD]
);

val MSB_THM3 = prove(
  `!a. ~(HB = 0) /\ ~MSB a ==> (w2n a = WORD_BITS (HB - 1) 0 a)`,
  STRIP_TAC THEN Cases_on_word `a`
    THEN RW_TAC bool_ss [MSB_EVAL,MSBn_def,w2n_EVAL,MOD_WL_THM,WORD_BITS_def,lem3]
    THEN IMP_RES_TAC BIT_SLICE_THM3
    THEN IMP_RES_TAC lem6 THEN POP_ASSUM (SPEC_THEN `n` ASSUME_TAC)
    THEN PAT_ASSUM `SLICE HB HB n = 0` (fn th => FULL_SIMP_TAC arith_ss [th,GSYM SLICE_ZERO_THM])
);

val MSB_THM4 = prove(
  `!a. ~(HB = 0) /\ ~(a = 0w) /\ ~MSB a ==>
       (w2n (word_2comp a) = 2 EXP WL - WORD_BITS (HB - 1) 0 a) /\ ~(WORD_BITS (HB - 1) 0 a = 0)`,
  STRIP_TAC THEN Cases_on_word `a`
    THEN REPEAT STRIP_TAC THEN IMP_RES_TAC MSB_THM3
    THEN FULL_SIMP_TAC bool_ss [MSB_EVAL,MSBn_def,w2n_EVAL,MOD_WL_THM,WORD_BITS_def,BITS_ZERO2,
                                n2w_11,TWO_COMP_EVAL,TWO_COMP_def,lem3]
    THEN FULL_SIMP_TAC arith_ss [BITS_COMP_THM2,MIN_DEF]
    THEN `2 ** WL - BITS (HB - 1) 0 n < 2 ** WL` by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
    THEN ASM_SIMP_TAC bool_ss [SPEC `HB` BITS_ZERO3,SYM WL_def,LESS_MOD]
);

val HB_0_MSB = prove(
  `!a. (HB = 0) /\ MSB a ==> (a = 1w)`,
  STRIP_TAC THEN Cases_on_word `a`
    THEN RW_TAC bool_ss [MSB_EVAL,MSBn_def,w2n_EVAL,word_1,n2w_11,MOD_WL_THM,BIT_def]
    THEN PAT_ASSUM `HB = 0` (fn th => FULL_SIMP_TAC arith_ss [th,BITS_ZERO3])
);

val HB_0_NOT_MSB = prove(
  `!a. (HB = 0) /\ ~MSB a ==> (a = 0w)`,
  STRIP_TAC THEN Cases_on_word `a`
    THEN RW_TAC bool_ss [MSB_EVAL,MSBn_def,w2n_EVAL,n2w_11,MOD_WL_THM,BIT_def,BITS_ZERO2]
    THEN PROVE_TAC [NOT_BITS2]
);

val MSB_THM1b = prove(
  `!a. (HB = 0) /\ MSB a ==> (w2n a = 1)`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC HB_0_MSB
    THEN ASM_SIMP_TAC arith_ss [word_1,w2n_EVAL,BITS_ZERO3,MOD_WL_THM]
);

val MSB_THM2b = prove(
  `!a. (HB = 0) /\ MSB a ==> (w2n (word_2comp a) = 1)`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC HB_0_MSB
    THEN ASM_SIMP_TAC arith_ss [word_1,w2n_EVAL,BITS_ZERO3,MOD_WL_THM,WL_def,TWO_COMP_EVAL,TWO_COMP_def]
);

val MSB_THM3b = prove(
  `!a. (HB = 0) /\ ~MSB a ==> (w2n a = 0)`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC HB_0_NOT_MSB
    THEN ASM_SIMP_TAC arith_ss [w2n_EVAL,BITS_ZERO3,MOD_WL_THM]
);

val MSB_THM4b = prove(
  `!a. (HB = 0) /\ ~MSB a ==> (w2n (word_2comp a) = 0)`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC HB_0_NOT_MSB
    THEN ASM_REWRITE_TAC [WORD_NEG_0]
    THEN REWRITE_TAC [w2n_EVAL,BITS_ZERO2,MOD_WL_THM]
);

(* -------------------------------------------------------- *)

val lem4a = prove(
  `!b a. ~(b = 0) ==> WORD_BITS (b - 1) 0 a < 2 EXP b`,
  REPEAT STRIP_TAC
    THEN POP_ASSUM (fn th => REWRITE_TAC [(SIMP_RULE arith_ss [lem8,th] o
                                            SPECL [`b - 1`,`0`,`a`]) WORD_BITSLT_THM])
);

val lem4b = prove(
  `!b a. ~(b = 0) ==> SLICE (b - 1) 0 a < 2 EXP b`,
  REPEAT STRIP_TAC
    THEN POP_ASSUM (fn th => REWRITE_TAC [SLICE_ZERO_THM,(SIMP_RULE arith_ss [lem8,th] o
                                            SPECL [`b - 1`,`0`,`a`]) BITSLT_THM])
);

val lem4 = prove(
  `!b a. ~(b = 0) ==> WORD_BITS (b - 1) 0 a <= 2 EXP b`,
  PROVE_TAC [LESS_IMP_LESS_OR_EQ,lem4a]
);

val TWO_COMP_POS = store_thm("TWO_COMP_POS",
  `!a. ~MSB a ==> (if a = 0w then ~MSB (word_2comp a) else MSB (word_2comp a))`,
  RW_TAC bool_ss [WORD_NEG_0]
    THEN Cases_on `HB = 0` THEN1 PROVE_TAC [HB_0_NOT_MSB]
    THEN REPEAT (POP_ASSUM MP_TAC) THEN Cases_on_word `a`
    THEN REPEAT STRIP_TAC THEN IMP_RES_TAC MSB_THM4 THEN IMP_RES_TAC w2n_n2w
    THEN ASM_SIMP_TAC arith_ss [BITS_COMP_THM2,MIN_DEF,MSB_EVAL,MOD_WL_THM,MSBn_def,BIT_def]
    THEN `2 EXP HB - WORD_BITS (HB - 1) 0 (n2w n) < 2 EXP HB` by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
    THEN IMP_RES_TAC lem4
    THEN ASM_SIMP_TAC bool_ss [BITS_THM,SUC_SUB,EXP_1,SPLIT_2_EXP_WL,LESS_EQ_ADD_SUB,DIV_MULT_1]
    THEN REDUCE_TAC
);

val lem2 = prove(
  `!n. ~(HB = 0) /\ ~(n2w n = word_L) /\ MSB (n2w n) ==> ~(WORD_BITS (HB - 1) 0 (n2w n) = 0)`,
  RW_TAC arith_ss [BITS_COMP_THM2,MIN_DEF,MSB_EVAL,MSBn_def,WORD_BITS_def,w2n_EVAL,MOD_WL_THM]
    THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
    THEN IMP_RES_TAC BIT_SLICE_THM2
    THEN RULE_ASSUM_TAC (REWRITE_RULE [GSYM SLICE_ZERO_THM])
    THEN IMP_RES_TAC lem6 THEN POP_ASSUM (SPEC_THEN `n` ASSUME_TAC)
    THEN FULL_SIMP_TAC bool_ss [word_L_def,n2w_11,MOD_WL_THM,BITS_ZERO3,LESS_MOD,SPEC_LESS_EXP_SUC_MONO]
    THEN FULL_SIMP_TAC bool_ss [GSYM BITS_ZERO3,GSYM SLICE_ZERO_THM]
    THEN PROVE_TAC [ADD_0]
);

val TWO_COMP_NEG = store_thm("TWO_COMP_NEG",
  `!a. MSB a ==> if (HB = 0) \/ (a = word_L) then MSB (word_2comp a) else ~MSB (word_2comp a)`,
  RW_TAC bool_ss []
    THENL [
      IMP_RES_TAC HB_0_MSB
        THEN ASM_REWRITE_TAC [MSB_EVAL,MSB_COMP0,WORD_NEG_1,word_T_def],
      ASM_REWRITE_TAC [WORD_NEG_L],
      FULL_SIMP_TAC bool_ss []
        THEN REPEAT (POP_ASSUM MP_TAC) THEN Cases_on_word `a`
        THEN NTAC 3 STRIP_TAC THEN IMP_RES_TAC MSB_THM2 THEN IMP_RES_TAC w2n_n2w
        THEN ASM_SIMP_TAC arith_ss [BITS_COMP_THM2,MIN_DEF,MSB_EVAL,MOD_WL_THM,MSBn_def,BIT_def]
        THEN IMP_RES_TAC lem2
        THEN `2 EXP HB - WORD_BITS (HB -1) 0 (n2w n) < 2 EXP HB` by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
        THEN ASM_SIMP_TAC arith_ss [BITS_THM,SUC_SUB,EXP_1,LESS_DIV_EQ_ZERO]
    ]
);

val TWO_COMP_POS_NEG = store_thm("TWO_COMP_POS_NEG",
  `!a. ~((HB = 0) \/ (a = 0w) \/ (a = word_L)) ==> (~MSB a = MSB (word_2comp a))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
    THEN1 PROVE_TAC [TWO_COMP_POS]
    THEN PROVE_TAC [(REWRITE_RULE [WORD_NEG_L,WORD_NEG_EQ,WORD_NEG_NEG] o SPEC `word_2comp a`) TWO_COMP_NEG]
);

val TWO_COMP_NEG_POS = store_thm("TWO_COMP_NEG_POS",
  `!a. ~((HB = 0) \/ (a = 0w) \/ (a = word_L)) ==> (MSB a = ~MSB (word_2comp a))`,
  PROVE_TAC [(REWRITE_RULE [WORD_NEG_L,WORD_NEG_EQ,WORD_NEG_0,WORD_NEG_NEG] o
              SPEC `word_2comp a`) TWO_COMP_POS_NEG]
);

val WORD_0_POS = store_thm("WORD_0_POS",
  `~MSB 0w`,
  REWRITE_TAC [MSB_EVAL,MSBn_def,BIT_ZERO]
);

val WORD_H_POS = store_thm("WORD_H_POS",
  `~MSB word_H`,
  `2 ** HB - 1 < 2 ** HB` by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
     THEN ASM_SIMP_TAC arith_ss [word_H_def,MSB_EVAL,MSBn_def,BIT_def,BITS_THM,
            LESS_DIV_EQ_ZERO,ZERO_MOD,ZERO_LT_TWOEXP]
);

val WORD_L_NEG = store_thm("WORD_L_NEG",
  `MSB word_L`,
  REWRITE_TAC [word_L_def,MSB_EVAL,MSBn_def,BIT_ZERO,BIT_B]
);

(* -------------------------------------------------------- *)

val NOT_EQUAL_THEN_NOT = PROVE [EQUAL_THEN_SUB_ZERO] `!a b. ~(a = b) = ~(b - a = 0w)`;

val ADD_EVAL3 = prove(
  `!a b. a + b = n2w (w2n a + w2n b)`,
  REWRITE_TAC [GSYM ADD_EVAL,w2n_ELIM]
);

val SUB_EQUAL_WORD_L_MSB = prove(
  `!a b. ~(HB = 0) /\ (a - b = word_L) ==> ~(MSB a = MSB b)`,
  RW_TAC bool_ss [WORD_EQ_SUB_RADD]
    THEN Cases_on_word `b`
    THEN REWRITE_TAC [MSB_EVAL,MSBn_def,word_L_def]
    THEN SUBST1_TAC ((SYM o SPEC `n`) MOD_WL_ELIM)
    THEN REWRITE_TAC [ADD_EVAL,MOD_WL_THM,MSB_EVAL,MSBn_def]
    THEN Cases_on `BIT HB n`
    THEN IMP_RES_TAC BIT_SLICE_THM2
    THEN IMP_RES_TAC BIT_SLICE_THM3
    THEN IMP_RES_TAC lem6
    THEN POP_ASSUM (fn th => ASM_SIMP_TAC arith_ss [GSYM SLICE_ZERO_THM,(SYM o SPEC `n`) th])
    THEN ASM_SIMP_TAC bool_ss [BIT_def,BITS_THM,SUC_SUB,EXP_1,lem4b,DIV_MULT,DIV_MULT_1]
    THEN REDUCE_TAC
);

val LEM1_TAC =
  REPEAT STRIP_TAC
    THEN Cases_on `MSB a`
    THEN Cases_on `MSB b`
    THEN Cases_on `a = b`
    THEN FULL_SIMP_TAC bool_ss [WORD_LT,WORD_GT,WORD_LE,WORD_GE,WORD_SUB_REFL,WORD_0_POS,DECIDE (Term `~(a = ~a)`)]
    THEN GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM WORD_NEG_SUB]
    THEN IMP_RES_TAC NOT_EQUAL_THEN_NOT
    THEN Cases_on `b - a = word_L`
    THEN PROVE_TAC [SUB_EQUAL_WORD_L_MSB,TWO_COMP_POS_NEG];

val LEM2_TAC =
  REPEAT STRIP_TAC
    THEN Cases_on `MSB a`
    THEN Cases_on `MSB b`
    THEN IMP_RES_TAC MSB_THM1b
    THEN IMP_RES_TAC MSB_THM2b
    THEN IMP_RES_TAC MSB_THM3b
    THEN IMP_RES_TAC MSB_THM4b
    THEN ASM_SIMP_TAC arith_ss [WORD_LT,WORD_GT,WORD_LE,WORD_GE,word_sub_def,
                                ADD_EVAL3,ADD_EVAL,MSB_EVAL,MSBn_def,
                                n2w_11,MOD_WL_THM,BITS_ZERO2,BIT_def]
    THEN ASM_SIMP_TAC arith_ss [BITS_ZERO3]
    THEN PROVE_TAC [w2n_11];

val WORD_GREATER = store_thm("WORD_GREATER",
  `!a b. word_gt a b = word_lt b a`,
  Cases_on `HB = 0` THENL [LEM2_TAC,LEM1_TAC]
);

val WORD_GREATER_EQ = store_thm("WORD_GREATER_EQ",
  `!a b. word_ge a b = word_le b a`,
  Cases_on `HB = 0` THENL [LEM2_TAC,LEM1_TAC]
);

val WORD_NOT_LESS = store_thm("WORD_NOT_LESS",
  `!a b. ~(word_lt a b) = word_le b a`,
  Cases_on `HB = 0` THENL [LEM2_TAC,LEM1_TAC]
);

val WORD_NOT_LESS_EQUAL = store_thm("WORD_NOT_LESS_EQUAL",
  `!a b. ~(word_le a b) = word_lt b a`,
  PROVE_TAC [WORD_NOT_LESS]
);

val WORD_LESS_OR_EQ = store_thm("WORD_LESS_OR_EQ",
  `!a b. word_le a b = word_lt a b \/ (a = b)`,
  LEM1_TAC
);

val WORD_GREATER_OR_EQ = store_thm("WORD_GREATER_OR_EQ",
  `!a b. word_ge a b = word_gt a b \/ (a = b)`,
  PROVE_TAC [WORD_GREATER,WORD_GREATER_EQ,WORD_LESS_OR_EQ]
);

(* -------------------------------------------------------- *)

val LESS_EQ_ADD2 = DECIDE (Term `!a b c. a + b <= a + c ==> b <= c`);
val LESS_ADD2 = DECIDE (Term `!a b c. a + b < a + c ==> b < c`);

val lem5 = DECIDE (Term `!m n p. p <= n ==> (m + p - n = m - (n - p))`);

val lem9 = prove(
  `!a b. ~(HB = 0) /\ MSB a /\ MSB b /\ MSB (a - b) ==> w2n a < w2n b`,
  REWRITE_TAC [word_sub_def,ADD_EVAL3]
    THEN RW_TAC bool_ss [MSB_EVAL,MSBn_def]
    THEN POP_ASSUM MP_TAC
    THEN Cases_on `w2n a < w2n b` THEN ASM_REWRITE_TAC []
    THEN IMP_RES_TAC MSB_THM1
    THEN `w2n ~b = 2 ** HB - WORD_BITS (HB - 1) 0 b` by IMP_RES_TAC MSB_THM2
    THEN FULL_SIMP_TAC bool_ss [NOT_LESS,GSYM LESS_EQ_ADD_SUB,DECIDE (Term `!a b. a + b + a = 2 * a + b`),lem4]
    THEN IMP_RES_TAC LESS_EQ_ADD2
    THEN ASM_SIMP_TAC bool_ss [lem5,BIT_def,BITS_THM,SUC_SUB,EXP_1,LESS_EQ_ADD_SUB]
    THEN IMP_RES_TAC lem4a
    THEN POP_ASSUM (SPEC_THEN `a` ASSUME_TAC)
    THEN ASSUME_TAC (SPECL [`WORD_BITS (HB - 1) 0 a`,`WORD_BITS (HB - 1) 0 b`] SUB_LESS_EQ)
    THEN `WORD_BITS (HB - 1) 0 a - WORD_BITS (HB - 1) 0 b < 2 ** HB` by IMP_RES_TAC LESS_EQ_LESS_TRANS
    THEN ASM_SIMP_TAC arith_ss [DIV_MULT]
);

val lem10 = prove(
  `!a b. ~(HB = 0) /\ MSB a /\ MSB b /\ ~MSB (a - b) ==> ~(w2n a < w2n b)`,
  REWRITE_TAC [word_sub_def,ADD_EVAL3]
    THEN RW_TAC bool_ss [MSB_EVAL,MSBn_def]
    THEN POP_ASSUM MP_TAC
    THEN Cases_on `w2n a < w2n b` THEN ASM_REWRITE_TAC []
    THEN IMP_RES_TAC MSB_THM1
    THEN `w2n ~b = 2 ** HB - WORD_BITS (HB - 1) 0 b` by IMP_RES_TAC MSB_THM2
    THEN FULL_SIMP_TAC bool_ss [GSYM LESS_EQ_ADD_SUB,lem4]
    THEN ONCE_REWRITE_TAC [DECIDE (Term `!a b c. (a:num) + b + c = a + c + b`)]
    THEN PAT_ASSUM `x + y < x + z` (ASSUME_TAC o (MATCH_MP LESS_ADD2))
    THEN IMP_RES_TAC LESS_ADD_1
    THEN IMP_RES_TAC lem4a
    THEN POP_ASSUM (SPEC_THEN `b` ASSUME_TAC)
    THEN `p + 1 <= 2 EXP HB` by DECIDE_TAC
    THEN ASM_SIMP_TAC bool_ss [SUB_PLUS,ADD_SUB]
    THEN ASM_SIMP_TAC bool_ss [GSYM SUB_PLUS,LESS_EQ_ADD_SUB]
    THEN `2 EXP HB - (p + 1) < 2 EXP HB` by DECIDE_TAC
    THEN ASM_SIMP_TAC bool_ss [BIT_def,BITS_THM,DIV_MULT_1,SUC_SUB,EXP_1]
    THEN REDUCE_TAC
);

val w2n_0w = SIMP_CONV arith_ss [w2n_EVAL,MOD_WL_THM,BITS_ZERO2] (Term `w2n 0w`);

val lem11 = prove(
  `!a b. ~(HB = 0) /\ ~MSB a /\ ~MSB b /\ MSB (a - b) ==> w2n a < w2n b`,
  REWRITE_TAC [word_sub_def,ADD_EVAL3]
    THEN NTAC 2 STRIP_TAC
    THEN Cases_on `b = 0w`
    THENL [
      ASM_REWRITE_TAC [WORD_NEG_0,w2n_0w,ADD_0,w2n_ELIM] THEN DECIDE_TAC,
      RW_TAC bool_ss [MSB_EVAL,MSBn_def]
        THEN POP_ASSUM MP_TAC
        THEN Cases_on `w2n a < w2n b` THEN ASM_REWRITE_TAC []
        THEN IMP_RES_TAC MSB_THM3
        THEN `w2n ~b = 2 ** WL - WORD_BITS (HB - 1) 0 b` by IMP_RES_TAC MSB_THM4
        THEN IMP_RES_TAC lem4
        THEN POP_ASSUM (SPEC_THEN `b` ASSUME_TAC)
        THEN ASSUME_TAC
             (MATCH_MP LESS_IMP_LESS_OR_EQ ((REWRITE_RULE [SYM WL_def] o SPEC `HB`) SPEC_LESS_EXP_SUC_MONO))
        THEN `WORD_BITS (HB - 1) 0 b <= 2 ** WL` by IMP_RES_TAC LESS_EQ_TRANS
        THEN FULL_SIMP_TAC bool_ss [NOT_LESS,GSYM LESS_EQ_ADD_SUB]
        THEN ONCE_REWRITE_TAC [ADD_COMM]
        THEN IMP_RES_TAC lem4a
        THEN POP_ASSUM (SPEC_THEN `a` ASSUME_TAC)
        THEN `WORD_BITS (HB - 1) 0 a - WORD_BITS (HB - 1) 0 b < 2 ** HB` by DECIDE_TAC
        THEN ASM_SIMP_TAC bool_ss [BIT_def,BITS_THM,SUC_SUB,EXP_1,LESS_EQ_ADD_SUB,WL_def,EXP,DIV_MULT]
        THEN REDUCE_TAC
    ]
);

val lem12 = prove(
  `!a b. ~(HB = 0) /\ ~MSB a /\ ~MSB b /\ ~MSB (a - b) ==> ~(w2n a < w2n b)`,
  REWRITE_TAC [word_sub_def,ADD_EVAL3]
    THEN NTAC 2 STRIP_TAC
    THEN Cases_on `b = 0w` THEN1 ASM_SIMP_TAC arith_ss [w2n_0w]
    THEN RW_TAC bool_ss [MSB_EVAL,MSBn_def]
    THEN POP_ASSUM MP_TAC
    THEN Cases_on `w2n a < w2n b` THEN ASM_REWRITE_TAC []
    THEN IMP_RES_TAC MSB_THM3
    THEN IMP_RES_TAC MSB_THM4 THEN NTAC 4 (POP_ASSUM (K ALL_TAC))
    THEN IMP_RES_TAC lem4
    THEN POP_ASSUM (SPEC_THEN `b` ASSUME_TAC)
    THEN ASSUME_TAC
          (MATCH_MP LESS_IMP_LESS_OR_EQ ((REWRITE_RULE [SYM WL_def] o SPEC `HB`) SPEC_LESS_EXP_SUC_MONO))
    THEN `WORD_BITS (HB - 1) 0 b <= 2 ** WL` by IMP_RES_TAC LESS_EQ_TRANS
    THEN FULL_SIMP_TAC bool_ss [GSYM LESS_EQ_ADD_SUB]
    THEN ONCE_REWRITE_TAC [ADD_COMM]
    THEN `WORD_BITS (HB - 1) 0 b <= 2 ** HB + WORD_BITS (HB - 1) 0 a` by DECIDE_TAC
    THEN ASM_SIMP_TAC bool_ss [SPLIT_2_EXP_WL,GSYM ADD_ASSOC,LESS_EQ_ADD_SUB]
    THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
    THEN `2 ** HB - (WORD_BITS (HB - 1) 0 b - WORD_BITS (HB - 1) 0 a) < 2 ** HB` by DECIDE_TAC
    THEN ASM_SIMP_TAC bool_ss [lem5,DIV_MULT_1,BIT_def,BITS_THM,SUC_SUB,EXP_1]
    THEN REDUCE_TAC
);

val WORD_LT_THM = store_thm("WORD_LT_THM",
  `!a b. word_lt a b = (MSB a = MSB b) /\ w2n a < w2n b \/ MSB a /\ ~MSB b`,
  Cases_on `HB = 0`
    THEN REPEAT STRIP_TAC
    THENL [
      Cases_on `MSB a`
        THEN Cases_on `MSB b`
        THEN Cases_on `MSB (n2w (w2n a + w2n ~b))`
        THEN ASM_REWRITE_TAC [WORD_LT]
        THEN POP_ASSUM MP_TAC
        THEN Cases_on `w2n a < w2n b`
        THEN ASM_REWRITE_TAC [MSB_EVAL,MSBn_def,word_sub_def,ADD_EVAL3]
        THEN IMP_RES_TAC MSB_THM1b
        THEN IMP_RES_TAC MSB_THM2b
        THEN IMP_RES_TAC MSB_THM3b
        THEN IMP_RES_TAC MSB_THM4b
        THEN ASM_SIMP_TAC arith_ss [BIT_def,BITS_THM],
      Cases_on `MSB a`
        THEN Cases_on `MSB b`
        THEN Cases_on `MSB (a - b)`
        THEN ASM_SIMP_TAC bool_ss [WORD_LT,lem9,lem10,lem11,lem12]
    ]
);

val WORD_GT_THM = save_thm("WORD_GT_THM",
  (GEN `a` o GEN `b` o REWRITE_CONV [WORD_GREATER,WORD_LT_THM,GSYM GREATER_DEF]) (Term `word_gt a b`));

val WORD_LE_THM = store_thm("WORD_LE_THM",
  `!a b. word_le a b = (MSB a = MSB b) /\ (w2n a <= w2n b) \/ MSB a /\ ~MSB b`,
  RW_TAC bool_ss [WORD_LT_THM,GSYM WORD_NOT_LESS,NOT_LESS]
    THEN DECIDE_TAC
);

val WORD_GE_THM = save_thm("WORD_GE_THM",
  (GEN `a` o GEN `b` o REWRITE_CONV [WORD_GREATER_EQ,WORD_LE_THM,GSYM GREATER_EQ]) (Term `word_ge a b`));

val WORD_LESS_TRANS = store_thm("WORD_LESS_TRANS",
  `!a b c. word_lt a b /\ word_lt b c ==> word_lt a c`,
  RW_TAC bool_ss [WORD_LT_THM]
     THEN IMP_RES_TAC LESS_TRANS
     THEN ASM_REWRITE_TAC [] THEN PROVE_TAC []
);

val WORD_LESS_EQ_TRANS = store_thm("WORD_LESS_EQ_TRANS",
  `!a b c. word_le a b /\ word_le b c ==> word_le a c`,
  RW_TAC bool_ss [WORD_LE_THM]
     THEN IMP_RES_TAC LESS_EQ_TRANS
     THEN ASM_REWRITE_TAC [] THEN PROVE_TAC []
);

val WORD_LESS_EQ_LESS_TRANS = store_thm("WORD_LESS_EQ_LESS_TRANS",
  `!a b c. word_le a b /\ word_lt b c ==> word_lt a c`,
  RW_TAC bool_ss [WORD_LE_THM,WORD_LT_THM]
     THEN IMP_RES_TAC LESS_EQ_LESS_TRANS
     THEN ASM_REWRITE_TAC [] THEN PROVE_TAC []
);

val WORD_LESS_LESS_EQ_TRANS = store_thm("WORD_LESS_LESS_EQ_TRANS",
  `!a b c. word_lt a b /\ word_le b c ==> word_lt a c`,
  RW_TAC bool_ss [WORD_LE_THM,WORD_LT_THM]
     THEN IMP_RES_TAC LESS_LESS_EQ_TRANS
     THEN ASM_REWRITE_TAC [] THEN PROVE_TAC []
);

val WORD_LESS_EQ_CASES = store_thm("WORD_LESS_EQ_CASES",
  `!a b. word_le a b \/ word_le b a`,
  RW_TAC bool_ss [WORD_LE_THM]
    THEN PROVE_TAC [LESS_EQ_CASES]
);

val WORD_LESS_CASES = store_thm("WORD_LESS_CASES",
  `!a b. word_lt a b \/ word_le b a`,
  PROVE_TAC [WORD_LESS_OR_EQ,WORD_LESS_EQ_CASES]
);

val WORD_LESS_CASES_IMP = store_thm("WORD_LESS_CASES_IMP",
  `!a b. ~(word_lt a b) /\ ~(a = b) ==> word_lt b a`,
  PROVE_TAC [WORD_NOT_LESS,WORD_LESS_OR_EQ]
);

val WORD_LESS_ANTISYM = store_thm("WORD_LESS_ANTISYM",
  `!a b. ~(word_lt a b /\ word_lt b a)`,
  PROVE_TAC [WORD_NOT_LESS,WORD_LESS_EQ_CASES]
);

val WORD_LESS_EQ_ANTISYM = store_thm("WORD_LESS_EQ_ANTISYM",
  `!a b. ~(word_lt a b /\ word_le b a)`,
  PROVE_TAC [WORD_NOT_LESS]
);

val WORD_LESS_EQ_REFL = store_thm("WORD_LESS_EQ_REFL",
  `!a. word_le a a`,
  REWRITE_TAC [WORD_LESS_OR_EQ]
);

val WORD_LESS_EQUAL_ANTISYM = store_thm("WORD_LESS_EQUAL_ANTISYM",
  `!a b. word_le a b /\ word_le b a ==> (a = b)`,
  PROVE_TAC [WORD_LESS_OR_EQ,WORD_LESS_ANTISYM]
);

val WORD_LESS_IMP_LESS_OR_EQ = store_thm("WORD_LESS_IMP_LESS_OR_EQ",
  `!a b. word_lt a b ==> word_le a b`,
  PROVE_TAC [WORD_LESS_OR_EQ]
);

val WORD_LESS_REFL = store_thm("WORD_LESS_REFL",
  `!a. ~(word_lt a a)`,
  RW_TAC bool_ss [WORD_NOT_LESS,WORD_LESS_OR_EQ]
);

val WORD_LESS_LESS_CASES = store_thm("WORD_LESS_LESS_CASES",
  `!a b. (a = b) \/ word_lt a b \/ word_lt b a`,
  PROVE_TAC [WORD_LESS_CASES,WORD_LESS_OR_EQ]
);

val WORD_NOT_GREATER = store_thm("WORD_NOT_GREATER",
  `!a b. ~(word_gt a b) = word_le a b`,
  PROVE_TAC [WORD_GREATER,WORD_NOT_LESS]
);

val WORD_LESS_NOT_EQ = store_thm("WORD_LESS_NOT_EQ",
  `!a b. word_lt a b ==> ~(a = b)`,
  PROVE_TAC [WORD_LESS_REFL,WORD_LESS_OR_EQ]
);

val WORD_NOT_LESS_EQ = store_thm("WORD_NOT_LESS_EQ",
  `!a b. (a = b) ==> ~(word_lt a b)`,
  PROVE_TAC [WORD_LESS_REFL]
);

(* -------------------------------------------------------- *)

val w2n_word_L =
  SIMP_CONV arith_ss [word_L_def,w2n_EVAL,MOD_WL_THM,BITS_ZERO3,
                      LESS_MOD,SPEC_LESS_EXP_SUC_MONO] (Term `w2n word_L`);

val w2n_word_H = prove(
  `w2n word_H = 2 ** HB - 1`,
  `2 ** HB - 1 < 2 ** HB` by SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
    THEN ASSUME_TAC (SPEC `HB` SPEC_LESS_EXP_SUC_MONO)
    THEN IMP_RES_TAC LESS_TRANS
    THEN ASM_SIMP_TAC arith_ss [word_H_def,w2n_EVAL,MOD_WL_THM,BITS_ZERO3,LESS_MOD]
);

val WORD_L_PLUS_H = store_thm("WORD_L_PLUS_H",
  `word_L + word_H = word_T`,
  SIMP_TAC bool_ss [ADD_EVAL3,w2n_word_L,w2n_word_H,ONE_LT_EQ_TWOEXP,word_T,
                    SPLIT_2_EXP_WL,GSYM LESS_EQ_ADD_SUB]
);

val WORD_L_LESS_EQ = store_thm("WORD_L_LESS_EQ",
  `!a. word_le word_L a`,
  RW_TAC bool_ss [WORD_LE_THM,WORD_L_NEG,w2n_word_L]
    THEN Cases_on `MSB a` THEN ASM_REWRITE_TAC []
    THEN Cases_on `HB = 0`
    THENL [
      IMP_RES_TAC MSB_THM1b THEN ASM_SIMP_TAC arith_ss [],
      NTAC 2 (POP_ASSUM MP_TAC)
        THEN Cases_on_word `a`
        THEN RW_TAC bool_ss [w2n_EVAL,MOD_WL_THM,MSB_EVAL,MSBn_def]
        THEN IMP_RES_TAC BIT_SLICE_THM2
        THEN IMP_RES_TAC lem6
        THEN POP_ASSUM (fn th => ASM_SIMP_TAC arith_ss [GSYM SLICE_ZERO_THM,(SYM o SPEC `n`) th])
    ]
);

val WORD_LESS_EQ_H = store_thm("WORD_LESS_EQ_H",
  `!a. word_le a word_H`,
  RW_TAC bool_ss [WORD_LE_THM,WORD_H_POS,w2n_word_H]
    THEN Cases_on `MSB a` THEN ASM_REWRITE_TAC []
    THEN Cases_on `HB = 0`
    THENL [
      IMP_RES_TAC MSB_THM3b THEN ASM_SIMP_TAC arith_ss [],
      NTAC 2 (POP_ASSUM MP_TAC)
        THEN Cases_on_word `a`
        THEN RW_TAC bool_ss [w2n_EVAL,MOD_WL_THM,MSB_EVAL,MSBn_def]
        THEN IMP_RES_TAC BIT_SLICE_THM3
        THEN IMP_RES_TAC lem6
        THEN POP_ASSUM (fn th => ASM_SIMP_TAC arith_ss [GSYM SLICE_ZERO_THM,(SYM o SPEC `n`) th])
        THEN PROVE_TAC [lem4b,SUB_LESS_OR]
    ]
);

val WORD_NOT_L_EQ_H = prove(
  `~(word_L = word_H)`,
  SIMP_TAC arith_ss [GSYM w2n_11,w2n_word_L,w2n_word_H,GSYM ADD_EQ_SUB,ONE_LT_EQ_TWOEXP]
);

val WORD_L_LESS_H = store_thm("WORD_L_LESS_H",
  `word_lt word_L word_H`,
  PROVE_TAC [WORD_L_LESS_EQ,WORD_LESS_EQ_H,WORD_LESS_EQ_TRANS,WORD_NOT_L_EQ_H,WORD_LESS_OR_EQ]
);

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val w2n_TWO_COMP = prove(
  `!a. w2n (word_2comp a) = if a = 0w then 0 else 2 EXP WL - w2n a`,
  RW_TAC bool_ss [WORD_NEG_0,w2n_0w]
    THEN POP_ASSUM MP_TAC
    THEN Cases_on_word `a`
    THEN RW_TAC bool_ss [GSYM w2n_11,w2n_0w,w2n_EVAL,TWO_COMP_EVAL,TWO_COMP_def]
    THEN `2 ** WL - MOD_WL n < 2 ** WL` by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
    THEN ASM_SIMP_TAC bool_ss [REWRITE_RULE [LT_WL_def] MOD_WL_IDEM]
);

val EQ_WORD_0 = prove(
  `!a. (a = 0w) = (w2n a = 0)`,
  REWRITE_TAC [GSYM w2n_11,w2n_0w]
);

val NOT_EQ_WORD_0 = prove(
  `!a. ~(a = 0w) = ~(w2n a = 0)`,
  PROVE_TAC [EQ_WORD_0]
);

val WORD_LS_THM = store_thm("WORD_LS_THM",
  `!a b. word_ls a b = w2n a <= w2n b`,
  RW_TAC bool_ss [WORD_LS]
    THEN Cases_on `b = 0w`
    THEN ASM_SIMP_TAC arith_ss [w2n_TWO_COMP,GSYM LESS_EQ_ADD_SUB,w2n_0w,EQ_WORD_0,
                                MATCH_MP LESS_IMP_LESS_OR_EQ (SPEC `b` w2n_LT)]
    THEN Cases_on `a = b` THEN1 ASM_SIMP_TAC arith_ss [BIT_B]
    THEN Cases_on `w2n a <= w2n b` THEN ASM_REWRITE_TAC []
    THEN ONCE_REWRITE_TAC [ADD_COMM]
    THEN RULE_ASSUM_TAC (REWRITE_RULE [GSYM w2n_11,w2n_0w,w2n_ELIM])
    THENL [
      `~(w2n b - w2n a = 0)` by DECIDE_TAC
        THEN POP_ASSUM (fn th => `2 ** WL - (w2n b - w2n a) < 2 ** WL` by SIMP_TAC arith_ss [th,ZERO_LT_TWOEXP])
        THEN ASM_SIMP_TAC arith_ss [GSYM SUB_SUB,BIT_def,BITS_THM,SUC_SUB,EXP_1,LESS_DIV_EQ_ZERO],
      RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS_EQUAL])
        THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
        THEN ASSUME_TAC (SPEC `a` w2n_LT)
        THEN `w2n a - w2n b < 2 ** WL` by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
        THEN ASM_SIMP_TAC bool_ss [LESS_EQ_ADD_SUB,BIT_def,BITS_THM,SUC_SUB,EXP_1,DIV_MULT_1]
        THEN REDUCE_TAC
   ]
);

val WORD_HI_THM = store_thm("WORD_HI_THM",
  `!a b. word_hi a b = w2n a > w2n b`,
  RW_TAC bool_ss [WORD_HI]
    THEN Cases_on `b = 0w`
    THEN ASM_SIMP_TAC arith_ss [w2n_TWO_COMP,GSYM LESS_EQ_ADD_SUB,w2n_0w,GREATER_DEF,NOT_EQ_WORD_0,
                                MATCH_MP LESS_IMP_LESS_OR_EQ (SPEC `b` w2n_LT)]
    THEN Cases_on `a = b` THEN1 ASM_SIMP_TAC arith_ss [BIT_B]
    THEN Cases_on `w2n a <= w2n b` THEN ASM_SIMP_TAC arith_ss []
    THEN ONCE_REWRITE_TAC [ADD_COMM]
    THEN RULE_ASSUM_TAC (REWRITE_RULE [GSYM w2n_11,w2n_0w,w2n_ELIM])
    THENL [
      `~(w2n b - w2n a = 0)` by DECIDE_TAC
        THEN POP_ASSUM (fn th => `2 ** WL - (w2n b - w2n a) < 2 ** WL` by SIMP_TAC arith_ss [th,ZERO_LT_TWOEXP])
        THEN ASM_SIMP_TAC arith_ss [GSYM SUB_SUB,BIT_def,BITS_THM,SUC_SUB,EXP_1,LESS_DIV_EQ_ZERO],
      RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS_EQUAL])
        THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
        THEN ASSUME_TAC (SPEC `a` w2n_LT)
        THEN `w2n a - w2n b < 2 ** WL` by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
        THEN ASM_SIMP_TAC bool_ss [LESS_EQ_ADD_SUB,BIT_def,BITS_THM,SUC_SUB,EXP_1,DIV_MULT_1]
        THEN REDUCE_TAC
    ]
);

val WORD_LO_THM = store_thm("WORD_LO_THM",
  `!a b. word_lo a b = w2n a < w2n b`,
  RW_TAC bool_ss [WORD_LO]
    THEN Cases_on `b = 0w`
    THEN ASM_SIMP_TAC arith_ss [w2n_TWO_COMP,GSYM LESS_EQ_ADD_SUB,w2n_0w,
                                MATCH_MP LESS_IMP_LESS_OR_EQ (SPEC `b` w2n_LT)]
    THEN Cases_on `a = b` THEN1 ASM_SIMP_TAC arith_ss [BIT_B]
    THEN Cases_on `w2n a < w2n b` THEN ASM_REWRITE_TAC []
    THEN ONCE_REWRITE_TAC [ADD_COMM]
    THEN RULE_ASSUM_TAC (REWRITE_RULE [GSYM w2n_11,w2n_0w,w2n_ELIM])
    THENL [
      IMP_RES_TAC LESS_IMP_LESS_OR_EQ
        THEN `~(w2n b - w2n a = 0)` by DECIDE_TAC
        THEN POP_ASSUM (fn th => `2 ** WL - (w2n b - w2n a) < 2 ** WL` by SIMP_TAC arith_ss [th,ZERO_LT_TWOEXP])
        THEN ASM_SIMP_TAC arith_ss [GSYM SUB_SUB,BIT_def,BITS_THM,SUC_SUB,EXP_1,LESS_DIV_EQ_ZERO],
      RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS])
        THEN ASSUME_TAC (SPEC `a` w2n_LT)
        THEN `w2n a - w2n b < 2 ** WL` by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
        THEN ASM_SIMP_TAC bool_ss [LESS_EQ_ADD_SUB,BIT_def,BITS_THM,SUC_SUB,EXP_1,DIV_MULT_1]
        THEN REDUCE_TAC
   ]
);

val WORD_HS_THM = store_thm("WORD_HS_THM",
  `!a b. word_hs a b = w2n a >= w2n b`,
  RW_TAC bool_ss [WORD_HS]
    THEN Cases_on `b = 0w`
    THEN ASM_SIMP_TAC arith_ss [w2n_TWO_COMP,GSYM LESS_EQ_ADD_SUB,w2n_0w,GREATER_EQ,
                                MATCH_MP LESS_IMP_LESS_OR_EQ (SPEC `b` w2n_LT)]
    THEN Cases_on `a = b` THEN1 ASM_SIMP_TAC arith_ss [BIT_B]
    THEN Cases_on `w2n a < w2n b` THEN ASM_SIMP_TAC arith_ss []
    THEN ONCE_REWRITE_TAC [ADD_COMM]
    THEN RULE_ASSUM_TAC (REWRITE_RULE [GSYM w2n_11,w2n_0w,w2n_ELIM])
    THENL [
      IMP_RES_TAC LESS_IMP_LESS_OR_EQ
        THEN `~(w2n b - w2n a = 0)` by DECIDE_TAC
        THEN POP_ASSUM (fn th => `2 ** WL - (w2n b - w2n a) < 2 ** WL` by SIMP_TAC arith_ss [th,ZERO_LT_TWOEXP])
        THEN ASM_SIMP_TAC arith_ss [GSYM SUB_SUB,BIT_def,BITS_THM,SUC_SUB,EXP_1,LESS_DIV_EQ_ZERO],
      RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS])
        THEN ASSUME_TAC (SPEC `a` w2n_LT)
        THEN `w2n a - w2n b < 2 ** WL` by ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
        THEN ASM_SIMP_TAC bool_ss [LESS_EQ_ADD_SUB,BIT_def,BITS_THM,SUC_SUB,EXP_1,DIV_MULT_1]
        THEN REDUCE_TAC
   ]
);

val WORD_HIGHER = prove(
  `!a b. word_hi a b = word_lo b a`,
  RW_TAC arith_ss [WORD_HI_THM,WORD_LO_THM]
);

val WORD_HIGHER_EQ = store_thm("WORD_HIGHER_EQ",
  `!a b. word_hs a b = word_ls b a`,
  RW_TAC arith_ss [WORD_HS_THM,WORD_LS_THM]
);

val WORD_NOT_LOWER = store_thm("WORD_NOT_LOWER",
  `!a b. ~(word_lo a b) = word_ls b a`,
  RW_TAC arith_ss [WORD_LO_THM,WORD_LS_THM]
);

val WORD_NOT_LOWER_EQUAL = store_thm("WORD_NOT_LOWER_EQUAL",
  `!a b. ~(word_ls a b) = word_lo b a`,
  PROVE_TAC [WORD_NOT_LOWER]
);

val WORD_LOWER_OR_EQ = store_thm("WORD_LOWER_OR_EQ",
  `!a b. word_ls a b = word_lo a b \/ (a = b)`,
  REWRITE_TAC [LESS_OR_EQ,WORD_LS_THM,WORD_LO_THM,w2n_11]
);

val WORD_HIGHER_OR_EQ = store_thm("WORD_HIGHER_OR_EQ",
  `!a b. word_hs a b = word_hi a b \/ (a = b)`,
  REWRITE_TAC [GREATER_OR_EQ,WORD_HS_THM,WORD_HI_THM,w2n_11]
);

val WORD_LOWER_TRANS = store_thm("WORD_LOWER_TRANS",
  `!a b c. word_lo a b /\ word_lo b c ==> word_lo a c`,
  PROVE_TAC [WORD_LO_THM,LESS_TRANS]
);

val WORD_LOWER_EQ_TRANS = store_thm("WORD_LOWER_EQ_TRANS",
  `!a b c. word_ls a b /\ word_ls b c ==> word_ls a c`,
  PROVE_TAC [WORD_LS_THM,LESS_EQ_TRANS]
);

val WORD_LOWER_EQ_LOWER_TRANS = store_thm("WORD_LOWER_EQ_LOWER_TRANS",
  `!a b c. word_ls a b /\ word_lo b c ==> word_lo a c`,
  PROVE_TAC [WORD_LS_THM,WORD_LO_THM,LESS_EQ_LESS_TRANS]
);

val WORD_LOWER_LOWER_EQ_TRANS = store_thm("WORD_LOWER_LOWER_EQ_TRANS",
  `!a b c. word_lo a b /\ word_ls b c ==> word_lo a c`,
  PROVE_TAC [WORD_LS_THM,WORD_LO_THM,LESS_LESS_EQ_TRANS]
);

val WORD_LOWER_EQ_CASES = store_thm("WORD_LOWER_EQ_CASES",
  `!a b. word_ls a b \/ word_ls b a`,
  RW_TAC bool_ss [WORD_LS_THM,LESS_EQ_CASES]
);

val WORD_LOWER_CASES = store_thm("WORD_LOWER_CASES",
  `!a b. word_lo a b \/ word_ls b a`,
  PROVE_TAC [WORD_LOWER_OR_EQ,WORD_LOWER_EQ_CASES]
);

val WORD_LOWER_CASES_IMP = store_thm("WORD_LOWER_CASES_IMP",
  `!a b. ~(word_lo a b) /\ ~(a = b) ==> word_lo b a`,
  PROVE_TAC [WORD_NOT_LOWER,WORD_LOWER_OR_EQ]
);

val WORD_LOWER_ANTISYM = store_thm("WORD_LOWER_ANTISYM",
  `!a b. ~(word_lo a b /\ word_lo b a)`,
  PROVE_TAC [WORD_NOT_LOWER,WORD_LOWER_EQ_CASES]
);

val WORD_LOWER_EQ_ANTISYM = store_thm("WORD_LOWER_EQ_ANTISYM",
  `!a b. ~(word_lo a b /\ word_ls b a)`,
  PROVE_TAC [WORD_NOT_LOWER]
);

val WORD_LOWER_EQ_REFL = store_thm("WORD_LOWER_EQ_REFL",
  `!a. word_ls a a`,
  REWRITE_TAC [WORD_LOWER_OR_EQ]
);

val WORD_LOWER_EQUAL_ANTISYM = store_thm("WORD_LOWER_EQUAL_ANTISYM",
  `!a b. word_ls a b /\ word_ls b a ==> (a = b)`,
  PROVE_TAC [WORD_LOWER_OR_EQ,WORD_LOWER_ANTISYM]
);

val WORD_LOWER_IMP_LOWER_OR_EQ = store_thm("WORD_LOWER_IMP_LOWER_OR_EQ",
  `!a b. word_lo a b ==> word_ls a b`,
  PROVE_TAC [WORD_LOWER_OR_EQ]
);

val WORD_LOWER_REFL = store_thm("WORD_LOWER_REFL",
  `!a. ~(word_lo a a)`,
  RW_TAC bool_ss [WORD_NOT_LOWER,WORD_LOWER_OR_EQ]
);

val WORD_LOWER_LOWER_CASES = store_thm("WORD_LOWER_LOWER_CASES",
  `!a b. (a = b) \/ word_lo a b \/ word_lo b a`,
  PROVE_TAC [WORD_LOWER_CASES,WORD_LOWER_OR_EQ]
);

val WORD_NOT_HIGHER = store_thm("WORD_NOT_HIGHER",
  `!a b. ~(word_hi a b) = word_ls a b`,
  PROVE_TAC [WORD_HIGHER,WORD_NOT_LOWER]
);

val WORD_LOWER_NOT_EQ = store_thm("WORD_LOWER_NOT_EQ",
  `!a b. word_lo a b ==> ~(a = b)`,
  PROVE_TAC [WORD_LOWER_REFL,WORD_LOWER_OR_EQ]
);

val WORD_NOT_LOWER_EQ = store_thm("WORD_NOT_LOWER_EQ",
  `!a b. (a = b) ==> ~(word_lo a b)`,
  PROVE_TAC [WORD_LOWER_REFL]
);

(* -------------------------------------------------------- *)

val w2n_word_T = prove(
  `w2n word_T = 2 ** WL - 1`,
  `2 ** WL - 1 < 2 ** WL` by SIMP_TAC arith_ss [ZERO_LT_TWOEXP]
    THEN ASM_SIMP_TAC arith_ss [word_T,w2n_EVAL,MOD_WL_THM,GSYM WL_def,BITS_ZERO3,LESS_MOD]
);

val WORD_ZERO_LOWER_EQ = store_thm("WORD_ZERO_LOWER_EQ",
  `!a. word_ls 0w a`,
  RW_TAC arith_ss [WORD_LS_THM,w2n_0w]
);

val WORD_LOWER_EQ_T = store_thm("WORD_LOWER_EQ_T",
  `!a. word_ls a word_T`,
  RW_TAC bool_ss [WORD_LS_THM,w2n_word_T]
    THEN PROVE_TAC [w2n_LT,SUB_LESS_OR]
);

val WORD_NOT_ZERO_EQ_T = prove(
  `~(0w = word_T)`,
  SIMP_TAC arith_ss [GSYM w2n_11,w2n_0w,w2n_word_T,NOT_LESS_EQUAL,
                     DECIDE (Term `a < b = a <= b /\ ~(a = b)`),ONE_LT_EQ_TWOEXP]
    THEN SIMP_TAC arith_ss [WL_def,EXP,ZERO_LT_TWOEXP]
);

val WORD_ZERO_LOWER_T = store_thm("WORD_ZERO_LOWER_T",
  `word_lo 0w word_T`,
  PROVE_TAC [WORD_ZERO_LOWER_EQ,WORD_LOWER_EQ_T,WORD_LOWER_EQ_TRANS,WORD_NOT_ZERO_EQ_T,WORD_LOWER_OR_EQ]
);

(* -------------------------------------------------------- *)

val LT_EVAL = store_thm("LT_EVAL",
  `!m n. word_lt (n2w m) (n2w n) =
     let sm = MSBn m
     and sn = MSBn n
     in (sm = sn) /\ MOD_WL m < MOD_WL n \/ sm /\ ~sn`,
  RW_TAC std_ss [WORD_LT_THM,MSB_EVAL,w2n_EVAL]
);

val LE_EVAL = store_thm("LE_EVAL",
  `!m n. word_le (n2w m) (n2w n) =
     let sm = MSBn m
     and sn = MSBn n
     in (sm = sn) /\ MOD_WL m <= MOD_WL n \/ sm /\ ~sn`,
  RW_TAC std_ss [WORD_LE_THM,MSB_EVAL,w2n_EVAL]
);

val GT_EVAL = store_thm("GT_EVAL",
  `!m n. word_gt (n2w m) (n2w n) =
     let sm = MSBn m
     and sn = MSBn n
     in (sm = sn) /\ MOD_WL m > MOD_WL n \/ ~sm /\ sn`,
  RW_TAC std_ss [WORD_GT_THM,MSB_EVAL,w2n_EVAL] THEN DECIDE_TAC
);

val GE_EVAL = store_thm("GE_EVAL",
  `!m n. word_ge (n2w m) (n2w n) =
     let sm = MSBn m
     and sn = MSBn n
     in (sm = sn) /\ MOD_WL m >= MOD_WL n \/ ~sm /\ sn`,
  RW_TAC std_ss [WORD_GE_THM,MSB_EVAL,w2n_EVAL] THEN DECIDE_TAC
);

val LO_EVAL = store_thm("LO_EVAL",
  `!m n. word_lo (n2w m) (n2w n) = MOD_WL m < MOD_WL n`,
  RW_TAC bool_ss [WORD_LO_THM,w2n_EVAL]
);

val LS_EVAL = store_thm("LS_EVAL",
  `!m n. word_ls (n2w m) (n2w n) = MOD_WL m <= MOD_WL n`,
  RW_TAC bool_ss [WORD_LS_THM,w2n_EVAL]
);

val HI_EVAL = store_thm("HI_EVAL",
  `!m n. word_hi (n2w m) (n2w n) = MOD_WL m > MOD_WL n`,
  RW_TAC bool_ss [WORD_HI_THM,w2n_EVAL]
);

val HS_EVAL = store_thm("HS_EVAL",
  `!m n. word_hs (n2w m) (n2w n) = MOD_WL m >= MOD_WL n`,
  RW_TAC bool_ss [WORD_HS_THM,w2n_EVAL]
);

(*---------------------------------------------------------------------------*)
(* Support for termination proofs                                            *)
(*---------------------------------------------------------------------------*)

val ZERO_LESS_TWO_EXP = Q.prove
(`!n. 0 < 2**n`,
 METIS_TAC [ZERO_LESS_EXP,TWO]);

val ZERO_MOD_WL = Q.store_thm
("ZERO_MOD_WL",
 `0 MOD 2**WL = 0`,
 RW_TAC arith_ss [ZERO_MOD,ZERO_LESS_TWO_EXP]);

val lem = SIMP_RULE arith_ss [ZERO_LESS_TWO_EXP]
              (Q.SPEC `2**WL` bitsTheory.MOD_ADD_1);

val WORD_PRED_THM = Q.store_thm
("WORD_PRED_THM",
 `!m. ~(m = 0w) ==> w2n (m - 1w) < w2n m`,
 SIMP_TAC arith_ss [FORALL_WORD,w2n_EVAL]
  THEN Cases_on `n` THEN RW_TAC arith_ss []
  THEN POP_ASSUM MP_TAC
  THEN SIMP_TAC std_ss
         [ADD1,GSYM ADD_EVAL,WORD_ADD_SUB,w2n_EVAL,n2w_11]
  THEN RW_TAC std_ss [MOD_WL_def,ZERO_MOD_WL]
  THEN RW_TAC arith_ss [lem]);


val LT_DIV2 = Q.prove
(`!x. LT_WL x /\ 0<x ==> LT_WL (x DIV 2)`,
 RW_TAC arith_ss [LT_WL_def] THEN
  `1 < 2` by EVAL_TAC THEN
  `x DIV 2 < x` by METIS_TAC [DIV_LESS] THEN
  METIS_TAC [LESS_TRANS]);


val LSR1_LESS = Q.store_thm
("LSR1_LESS",
 `!w. ~(w = 0w) ==> w2n (w >>> 1) < w2n w`,
 SIMP_TAC arith_ss [FORALL_WORD,w2n_EVAL,LSR_EVAL,n2w_11]
   THEN RW_TAC std_ss []
   THEN `MOD_WL 0 = 0`
      by RW_TAC arith_ss [ZERO_MOD_WL,MOD_WL_def,bitsTheory.ZERO_LT_TWOEXP]
   THEN POP_ASSUM SUBST_ALL_TAC
   THEN `LT_WL (MOD_WL n)` by METIS_TAC [LT_WL_MOD_WL]
   THEN `0 < MOD_WL n` by RW_TAC arith_ss []
   THEN `LT_WL (MOD_WL n DIV 2)` by METIS_TAC [LT_DIV2]
   THEN RW_TAC arith_ss [DIV_LESS,MOD_WL_IDEM]);


val ZERO_SHIFT3 = Q.store_thm
("ZERO_SHIFT3",
 `!n. 0w >>> n = 0w`,
 RW_TAC arith_ss [n2w_11,LSR_EVAL,ZERO_MOD_WL,ZERO_DIV,
          MOD_WL_def,bitsTheory.ZERO_LT_TWOEXP]);

val LSR_LESS = Q.store_thm
("LSR_LESS",
 `!n w. ~(w = 0w) /\ 0 < n ==> w2n (w >>> n) < w2n w`,
 Induct THEN RW_TAC arith_ss []
   THEN `w >>> SUC n = (w >>> 1) >>> n`
         by METIS_TAC [ADD_CLAUSES,ONE,LSR_ADD]
   THEN POP_ASSUM SUBST_ALL_TAC
  THEN Cases_on `w>>>1 = 0w` THENL
  [RW_TAC arith_ss [ZERO_SHIFT3]
     THEN Q.PAT_ASSUM `~p` MP_TAC
     THEN Q.ID_SPEC_TAC `w`
     THEN SIMP_TAC arith_ss [FORALL_WORD,w2n_EVAL,n2w_11]
     THEN RW_TAC arith_ss [ZERO_MOD_WL,MOD_WL_def,bitsTheory.ZERO_LT_TWOEXP],
   Cases_on `n`
    THEN FULL_SIMP_TAC arith_ss []
    THEN METIS_TAC [ZERO_SHIFT2,LSR1_LESS,LESS_TRANS]]);


val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME
 (fn ppstrm => let
   val S = (fn s => (PP.add_string ppstrm s; PP.add_newline ppstrm))
 in
   S "val _ = TotalDefn.termination_simps := ";
   S "    LSR_LESS :: WORD_PRED_THM :: !TotalDefn.termination_simps";
   S " ";
   S "val _ = ";
   S "  let open Lib boolSyntax";
   S "      val word_type = type_of (fst(dest_forall(concl word_nchotomy)))";
   S "      val w2n_tm = fst(strip_comb(lhs(snd(dest_forall(concl w2n_def)))))";
   S "  in";
   S "  TypeBase.write";
   S "  [TypeBasePure.mk_nondatatype_info";
   S "   (word_type, ";
   S "     {nchotomy = SOME word_nchotomy,";
   S "      size = SOME (w2n_tm,CONJUNCT1(Drule.SPEC_ALL boolTheory.AND_CLAUSES)),";
   S "      encode=NONE})]";
   S "  end;"
 end)};

(* -------------------------------------------------------- *)

val _ = overload_on ("<",  Term`word_lt`);
val _ = overload_on ("<=", Term`word_le`);
val _ = overload_on (">",  Term`word_gt`);
val _ = overload_on (">=", Term`word_ge`);

val _ = overload_on ("<.",  Term`word_lo`);
val _ = overload_on ("<=.", Term`word_ls`);
val _ = overload_on (">.",  Term`word_hi`);
val _ = overload_on (">=.", Term`word_hs`);

val _ = add_infix("<.", 450,HOLgrammars.RIGHT);
val _ = add_infix("<=.",450,HOLgrammars.RIGHT);
val _ = add_infix(">.", 450,HOLgrammars.RIGHT);
val _ = add_infix(">=.",450,HOLgrammars.RIGHT);

(* -------------------------------------------------------- *)

val TOPNUM_DEF = new_definition("TOPNUM",`TOPNUM = 2**WL`);
val MAXNUM_DEF = new_definition("MAXNUM",`MAXNUM = TOPNUM - 1`);
val wH_def = new_definition("wH",`wH = 2**HB`);
val wL_def = new_definition("wL",`wL = 2**HB - 1`);
val fromNum = new_definition("fromNum", `fromNum n = n2w(MOD_WL n)`);
val toNum   = new_definition("toNum", `toNum = w2n`);
val _ =
 let open arithmeticTheory numeral_bitsTheory bitsTheory EmitML
     val THE_WL = SIMP_RULE arith_ss [HB_def,ADD1] WL_def
     val wL_thma = SIMP_RULE arith_ss [HB_def] wL_def
     val wH_thma = SIMP_RULE arith_ss [HB_def] wH_def
     val word_T_thm = SIMP_RULE arith_ss [THE_WL] word_T
     val TOPNUM_THMa = SIMP_RULE arith_ss [THE_WL] TOPNUM_DEF
     val MAXNUM_THMa = SIMP_RULE arith_ss [TOPNUM_THMa] MAXNUM_DEF
     val TOPNUM_THM = REWRITE_RULE[NUMERAL_DEF] TOPNUM_THMa
     val MAXNUM_THM = REWRITE_RULE[NUMERAL_DEF] MAXNUM_THMa
     val HB_THM = REWRITE_RULE[NUMERAL_DEF] HB_def
     val THE_WL_THM = REWRITE_RULE[NUMERAL_DEF] THE_WL
     val wL_thm = SIMP_RULE arith_ss [NUMERAL_DEF] wL_thma
     val wH_thm = SIMP_RULE arith_ss [NUMERAL_DEF] wH_thma
     val MOD_WL_EVAL = REWRITE_RULE [THE_WL,GSYM MOD_2EXP_def] MOD_WL_def
     val MSB_EVAL_THM = SIMP_RULE arith_ss
            [MSBn_def,HB_def,BIT_def,BITS_def,MOD_2EXP_def,
             GSYM ODD_MOD2_LEM] MSB_EVAL
     val LSB_EVAL_THMa = REWRITE_RULE [LSB_ODD] LSB_EVAL
     val LSB_EVAL_THM = Q.prove(`(LSB (n2w ZERO) = F) /\
                                 (LSB (n2w (BIT1 n)) = T) /\
                                 (LSB (n2w (BIT2 n)) = F)`,
         RW_TAC std_ss[LSB_EVAL_THMa,numeralTheory.numeral_evenodd])
     val ONE_COMP_THM = SIMP_RULE arith_ss [THE_WL,ONE_COMP_def] ONE_COMP_EVAL
     val TWO_COMP_THM = SIMP_RULE arith_ss [THE_WL,TWO_COMP_def] TWO_COMP_EVAL
     val OR_EVAL_THM = REWRITE_RULE [OR_def] OR_EVAL
     val AND_EVAL_THM = REWRITE_RULE [AND_def] AND_EVAL
     val EOR_EVAL_THM = REWRITE_RULE [EOR_def] EOR_EVAL
     val RRX_EVAL2 = SIMP_RULE arith_ss
           [GSYM DIV2_def,RRXn_def,LSR_ONE_def,HB_def,SBIT_def] RRX_EVAL
     val RRX_EVAL3 = CONJ (SIMP_RULE arith_ss [] (Thm.SPEC T (Q.ID_SPEC RRX_EVAL2)))
                          (SIMP_RULE arith_ss [] (Thm.SPEC F (Q.ID_SPEC RRX_EVAL2)))
     val ASR_EVAL = REWRITE_RULE [GSYM MOD_2EXP_def]
           (SIMP_RULE arith_ss [THE_WL,MSBn_def,BIT_def,BITS_def,SUC_SUB,
                 MOD_2EXP_def,GSYM ODD_MOD2_LEM,HB_def] ASR_THM);
     val LT_EVAL = REWRITE_RULE [MSBn_def,THE_WL,MOD_WL_EVAL] LT_EVAL
     val LE_EVAL = REWRITE_RULE [MSBn_def,THE_WL,MOD_WL_EVAL] LE_EVAL
     val GT_EVAL = REWRITE_RULE [MSBn_def,THE_WL,MOD_WL_EVAL] GT_EVAL
     val GE_EVAL = REWRITE_RULE [MSBn_def,THE_WL,MOD_WL_EVAL] GE_EVAL
     val LO_EVAL = REWRITE_RULE [MOD_WL_EVAL] LO_EVAL
     val LS_EVAL = REWRITE_RULE [MOD_WL_EVAL] LS_EVAL
     val HI_EVAL = REWRITE_RULE [MOD_WL_EVAL] HI_EVAL
     val HS_EVAL = REWRITE_RULE [MOD_WL_EVAL] HS_EVAL
     val wordn = "word"^sbits
     val WLstr = term_to_string (rhs(concl THE_WL))
     val HBstr = term_to_string (rhs(concl HB_def))
     val Lstr  = term_to_string (rhs(concl wL_thma))
     val Hstr  = term_to_string (rhs(concl wH_thma))
     val TOPstr = term_to_string (rhs(concl TOPNUM_THMa))
     val MAXstr = term_to_string (rhs(concl MAXNUM_THMa))
     val deNUMERAL = PURE_REWRITE_RULE[NUMERAL_DEF]
 in emitML MLdir
   (wordn,
    OPEN ["num", "bits", "numeral_bits"]
    :: EQDATATYPE ([],[QUOTE (wordn^" = n2w of num")])
    :: MLSIG "type num = numML.num"
    :: MLSTRUCT "nonfix - + * < > <= >= ;"
    :: MLSTRUCT (String.concat
        ["(*---------------------------------------------------------------------------\n",
         "         WL = ", WLstr, "\n",
         "         HB = ", HBstr, "\n",
         "         wL = ", Lstr, "\n",
         "         wH = ", Hstr, "\n",
         "     TOPNUM = ", TOPstr, "\n",
         "     MAXNUM = ", MAXstr, "\n",
         "  ---------------------------------------------------------------------------*)\n"])
    :: DEFN HB_THM :: DEFN WL_def
    :: DEFN (deNUMERAL TOPNUM_DEF)
    :: DEFN (deNUMERAL MAXNUM_DEF)
    :: DEFN (deNUMERAL wL_def)
    :: DEFN (deNUMERAL wH_def)
    :: map (DEFN o PURE_REWRITE_RULE [SYM HB_THM, SYM THE_WL_THM, SYM wL_thm, SYM wH_thm]
                 o PURE_REWRITE_RULE [NUMERAL_DEF, SYM TOPNUM_THM, SYM MAXNUM_THM])
       [word_T_thm, word_0, word_1,
        MOD_WL_EVAL,NUMERAL_DIV_2EXP,
        w2n_EVAL, MSB_EVAL_THM,  LSB_EVAL_THM,
        WORD_BIT_def, WORD_BITS_def, WORD_SLICE_def,
        ONE_COMP_THM, TWO_COMP_THM,
        OR_EVAL_THM, AND_EVAL_THM, EOR_EVAL_THM,
        ADD_EVAL2, MUL_EVAL2, word_sub_def,
        LSL_EVAL, LSR_THM, ASR_EVAL, ROR_THM, RRX_EVAL3,
        LT_EVAL, LE_EVAL, GT_EVAL, GE_EVAL,
        LO_EVAL, LS_EVAL, HI_EVAL, HS_EVAL,
        fromNum, toNum]
     @
     [MLSIG (String.concat["val fromBinString : string -> ",wordn]),
      MLSIG (String.concat["val fromOctString : string -> ",wordn]),
      MLSIG (String.concat["val fromDecString : string -> ",wordn]),
      MLSIG (String.concat["val fromHexString : string -> ",wordn]),
      MLSIG (String.concat["val toBinString : ",wordn, " -> string"]),
      MLSIG (String.concat["val toOctString : ",wordn, " -> string"]),
      MLSIG (String.concat["val toDecString : ",wordn, " -> string"]),
      MLSIG (String.concat["val toHexString : ",wordn, " -> string"]),
      MLSIG (String.concat["val ppBin : ppstream -> ",wordn, " -> unit"]),
      MLSIG (String.concat["val ppOct : ppstream -> ",wordn, " -> unit"]),
      MLSIG (String.concat["val ppDec : ppstream -> ",wordn, " -> unit"]),
      MLSIG (String.concat["val ppHex : ppstream -> ",wordn, " -> unit"]),
      MLSTRUCT "\n\
\ (*---------------------------------------------------------------------------*) \n\
\ (* Supplementary ML, not generated from HOL theorems, aimed at supporting    *) \n\
\ (* parsing and pretty printing of numerals.                                  *) \n\
\ (*---------------------------------------------------------------------------*) \n\
\  \n\
\ infix o; \n\
\ \n\
\ val fromBinString = fromNum o numML.fromBinString  \n\
\ val fromOctString = fromNum o numML.fromOctString  \n\
\ val fromDecString = fromNum o numML.fromDecString  \n\
\ val fromHexString = fromNum o numML.fromHexString; \n\
\  \n\
\ val toBinString = numML.toBinString o toNum; \n\
\ val toOctString = numML.toOctString o toNum; \n\
\ val toDecString = numML.toDecString o toNum; \n\
\ val toHexString = numML.toHexString o toNum; \n\
\  \n\
\ fun ppBin ppstrm w = numML.ppBin ppstrm (toNum w); \n\
\ fun ppOct ppstrm w = numML.ppOct ppstrm (toNum w); \n\
\ fun ppDec ppstrm w = numML.ppDec ppstrm (toNum w); \n\
\ fun ppHex ppstrm w = numML.ppHex ppstrm (toNum w); \n\n"])
 end;

val _ = export_theory();
val _ = export_theory_as_docfiles
          (fullPath[Systeml.HOLDIR,"src","n_bit","help","thms","wordn"]);

(* -------------------------------------------------------- *)

end
