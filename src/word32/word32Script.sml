(* app load ["bossLib","EquivType","pairTheory",
             "numeralTheory","selectUtil","bitsTheory"]; *)

infix 8 by;
infix THEN THENC THENL ++;

open HolKernel boolLib selectUtil Q Parse EquivType
     computeLib bossLib simpLib numLib pairTheory numeralTheory 
     arithmeticTheory prim_recTheory bitsTheory;

 
(* val arithr_ss = arith_ss++arithSimps.REDUCE_ss; *)
val arithr_ss = arith_ss;
val definition = fetch "-";

val PROVE = fn thl => fn q => PROVE thl (Term q);
  
val _ = set_fixity "EQUIVw" (Infixr 450);
val _ = set_fixity "ADDw" (Infixl 500);
val _ = set_fixity "SUBw" (Infixl 500);
val _ = set_fixity "MULw" (Infixl 550);
val _ = set_fixity "ORw" (Infixl 600);
val _ = set_fixity "EORw" (Infixl 600);
val _ = set_fixity "ANDw" (Infixl 650);

(* -------------------------------------------------------- *)
 
val _ = new_theory "word32";

(* -------------------------------------------------------- *)

val HB_def = Define`HB = 31`;

val WL_def = Define`WL = SUC HB`;

val WL_POS = REWRITE_RULE [SYM WL_def] (SPEC `HB` LESS_0);

val MODw_def = Define`MODw n = n MOD 2 EXP WL`;

val INw_def  = Define`INw n = n < 2 EXP WL`;

val EQUIVw_def = Define`x EQUIVw y = (MODw x = MODw y)`;

val EQUIVw_QT = store_thm("EQUIVw_QT",
  `!x y. x EQUIVw y = ($EQUIVw x = $EQUIVw y)`,
  REPEAT STRIP_TAC THEN EQ_TAC
    THEN RW_TAC std_ss [FUN_EQ_THM,EQUIVw_def,MODw_def]
);

val EQUIVw_RFL = PROVE [EQUIVw_QT] `!x. x EQUIVw x`;
val EQUIVw_SYM = PROVE [EQUIVw_QT] `!x y. x EQUIVw y = y EQUIVw x`;

(* -------------------------------------------------------- *)

val FUNPOW_THM = store_thm("FUNPOW_THM",
  `!f n x. FUNPOW f n (f x) = f (FUNPOW f n x)`,
  Induct_on `n` THEN ASM_REWRITE_TAC [FUNPOW]
);
 
val FUNPOW_THM2 = store_thm("FUNPOW_THM2",
  `!f n x. FUNPOW f (SUC n) x = f (FUNPOW f n x)`,
  Induct_on `n` THEN RW_TAC std_ss [FUNPOW,FUNPOW_THM]
);

val FUNPOW_EVAL = store_thm("FUNPOW_EVAL",
  `!f n x. FUNPOW f n x = if n = 0 then x else FUNPOW f (n-1) (f x)`,
  Induct_on `n` THEN RW_TAC arith_ss [FUNPOW]
);
 
(* -------------------------------------------------------- *)
 
val INw_MODw = store_thm("INw_MODw",
  `!n. INw (MODw n)`,
  RW_TAC arith_ss [ZERO_LT_TWOEXP,DIVISION,INw_def,MODw_def]
);

val TOw_IDEM = store_thm("TOw_IDEM",
  `!a. INw a ==> (MODw a = a)`,
  RW_TAC arith_ss [INw_def,MODw_def,LESS_MOD]
);

val MODw_IDEM2 = store_thm("MODw_IDEM2",
  `!a. MODw (MODw a) = MODw a`,
  RW_TAC std_ss [INw_MODw,TOw_IDEM]
);

val TOw_QT = store_thm("TOw_QT",
  `!a. MODw a EQUIVw a`,
  RW_TAC std_ss [EQUIVw_def,MODw_IDEM2]
);

val MODw_THM = store_thm("MODw_THM",
  `MODw = BITS HB 0`,
  ONCE_REWRITE_TAC [FUN_EQ_THM]
    THEN STRIP_TAC
    THEN REWRITE_TAC [MODw_def,WL_def,
       SIMP_CONV arith_ss [WL_def,BITS2_THM,CONJUNCT1 EXP,DIV1] 
                        ``BITS HB 0 n``]
);

(* -------------------------------------------------------- *)
 
val MOD_ADD = store_thm("MOD_ADD",
  `!a b. MODw (a + b) = MODw (MODw a + MODw b)`,
  RW_TAC std_ss [MODw_def,MOD_PLUS,ZERO_LT_TWOEXP]
);

val AONE_def = Define`AONE = 1`;

val ADD_QT = store_thm("ADD_QT",
  `(!n. 0 + n EQUIVw n) /\ !m n. SUC m + n EQUIVw SUC (m + n)`,
  RW_TAC arith_ss [EQUIVw_def,ADD]
);

val ADD_0_QT = store_thm("ADD_0_QT",
  `!a. a + 0 EQUIVw a`,
  RW_TAC arith_ss [EQUIVw_def]
);

val ADD_COMM_QT = store_thm("ADD_COMM_QT",
  `!a b. a + b EQUIVw b + a`,
  RW_TAC arith_ss [EQUIVw_def]
);

val ADD_ASSOC_QT = store_thm("ADD_ASSOC_QT",
  `!a b c. a + (b + c) EQUIVw a + b + c`,
  RW_TAC arith_ss [EQUIVw_def]
);

val MULT_QT = store_thm("MULT_QT",
  `(!n. 0 * n EQUIVw 0) /\ !m n. SUC m * n EQUIVw m * n + n`,
  RW_TAC arith_ss [EQUIVw_def,MULT]
);

val ADD1_QT = store_thm("ADD1_QT",
  `!m. SUC m EQUIVw m + AONE`,
  RW_TAC arith_ss [EQUIVw_def,ADD1,AONE_def]
);

val ADD_CLAUSES_QT = store_thm("ADD_CLAUSES_QT",
  `(!m. 0 + m EQUIVw m) /\ (!m. m + 0 EQUIVw m) /\ (!m n. SUC m + n EQUIVw SUC (m + n)) /\
      (!m n. m + SUC n EQUIVw SUC (m + n))`,
  RW_TAC arith_ss [EQUIVw_def,ADD_CLAUSES]
);

val MODw_0 = SIMP_CONV std_ss [ZERO_LT_TWOEXP,ZERO_MOD,MODw_def] ``MODw 0``;
val SPEC_MOD_TIMES = REWRITE_RULE [MULT_LEFT_1] (SPEC `1` (SIMP_RULE std_ss [ZERO_LT_TWOEXP]
                                                (SPEC `2 EXP WL` MOD_TIMES)));
val exp_gteq = REDUCE_RULE (MATCH_MP TWOEXP_MONO2 (SPEC `WL` ZERO_LESS_EQ));


val SUC_EQUIV_COMP = store_thm("SUC_EQUIV_COMP",
  `!a b. SUC a EQUIVw b ==> a EQUIVw (b + (2 EXP WL - 1))`,
  RW_TAC std_ss [EQUIVw_def]
    THEN ONCE_REWRITE_TAC [MOD_ADD]
    THEN POP_ASSUM (fn th => REWRITE_TAC [SYM th])
    THEN SIMP_TAC std_ss [MODw_def,GSYM MOD_ADD,ADD1,GSYM LESS_EQ_ADD_SUB,exp_gteq]
    THEN SIMP_TAC arith_ss [ONCE_REWRITE_RULE [ADD_COMM] SPEC_MOD_TIMES]
);

val INV_SUC_EQ_QT = store_thm("INV_SUC_EQ_QT",
  `!m n. (SUC m EQUIVw SUC n) = (m EQUIVw n)`,
  RW_TAC arith_ss [EQUIVw_def]
    THEN EQ_TAC
    THENL [
      RW_TAC std_ss []
        THEN IMP_RES_TAC (REWRITE_RULE [EQUIVw_def] SUC_EQUIV_COMP)
        THEN FULL_SIMP_TAC arithr_ss [GSYM LESS_EQ_ADD_SUB,ADD1,MODw_def,exp_gteq]
        THEN REWRITE_TAC [ONCE_REWRITE_RULE [ADD_COMM] SPEC_MOD_TIMES],
      REWRITE_TAC [ADD1]
        THEN ONCE_REWRITE_TAC [MOD_ADD]
        THEN RW_TAC std_ss []
    ]
);

val ADD_INV_0_QT = store_thm("ADD_INV_0_QT",
  `!m n. (m + n EQUIVw m) ==> (n EQUIVw 0)`,
  Induct_on `m`
    THEN RW_TAC std_ss [ADD_CLAUSES]
    THEN FULL_SIMP_TAC std_ss [INV_SUC_EQ_QT]
);

val ADD_INV_0_EQ_QT = store_thm("ADD_INV_0_EQ_QT",
  `!m n. (m + n EQUIVw m) = (n EQUIVw 0)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC
    THEN IMP_RES_TAC ADD_INV_0_QT
    THEN FULL_SIMP_TAC std_ss [EQUIVw_def]
    THEN ONCE_REWRITE_TAC [MOD_ADD]
    THEN ASM_SIMP_TAC arith_ss [MODw_0,MODw_IDEM2]
);

val EQ_ADD_LCANCEL_QT = store_thm("EQ_ADD_LCANCEL_QT",
  `!m n p. (m + n EQUIVw m + p) = (n EQUIVw p)`,
  Induct_on `m`
    THEN ASM_REWRITE_TAC [ADD_CLAUSES,INV_SUC_EQ_QT]
);

val EQ_ADD_RCANCEL_QT = store_thm("EQ_ADD_RCANCEL_QT",
  `!m n p. (m + p EQUIVw n + p) = (m EQUIVw n)`,
  ONCE_REWRITE_TAC[ADD_COMM] THEN MATCH_ACCEPT_TAC EQ_ADD_LCANCEL_QT
);

val LEFT_ADD_DISTRIB_QT = store_thm("LEFT_ADD_DISTRIB_QT",
  `!m n p. p * (m + n) EQUIVw p * m + p * n`,
  RW_TAC arith_ss [EQUIVw_def,LEFT_ADD_DISTRIB]
);

val MULT_ASSOC_QT = store_thm("MULT_ASSOC_QT",
  `!m n p. m * (n * p) EQUIVw m * n * p`,
  RW_TAC arith_ss [EQUIVw_def,MULT_ASSOC]
);

val MULT_COMM_QT = store_thm("MULT_COMM_QT",
  `!m n. m * n EQUIVw n * m`,
  RW_TAC arith_ss [EQUIVw_def,MULT_COMM]
);

val MULT_CLAUSES_QT = store_thm("MULT_CLAUSES_QT",
  `!m n. (0 * m EQUIVw 0) /\ (m * 0 EQUIVw 0) /\ (AONE * m EQUIVw m) /\ (m * AONE EQUIVw m) /\
         (SUC m * n EQUIVw m * n + n) /\ (m * SUC n EQUIVw m + m * n)`,
  RW_TAC arith_ss [EQUIVw_def,MULT_CLAUSES,AONE_def]
);

(* -------------------------------------------------------- *)

val MSB_def = Define`MSB = BIT HB`;
val ONE_COMP_def = Define`ONE_COMP x = 2 EXP WL - 1 - MODw x`;
val TWO_COMP_def = Define`TWO_COMP x = 2 EXP WL - MODw x`;
 
val MODw_LESS = REWRITE_RULE [MODw_def,INw_def] INw_MODw;

val ADD_TWO_COMP_QT = store_thm("ADD_TWO_COMP_QT",
  `!a. MODw a + TWO_COMP a EQUIVw 0`,
  RW_TAC arith_ss [TWO_COMP_def,EQUIVw_def,MODw_def]
   THEN ASSUME_TAC (SPEC `a` MODw_LESS)
   THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
   THEN ASM_SIMP_TAC std_ss [GSYM LESS_EQ_ADD_SUB]
   THEN ONCE_REWRITE_TAC [ADD_COMM]
   THEN SIMP_TAC std_ss [ADD_SUB,ZERO_MOD,DIVMOD_ID,ZERO_LT_TWOEXP]
);
 
val TWO_COMP_ONE_COMP_QT = store_thm("TWO_COMP_ONE_COMP_QT",
  `!a. TWO_COMP a EQUIVw ONE_COMP a + AONE`,
  STRIP_TAC THEN REWRITE_TAC [AONE_def]
    THEN ASSUME_TAC (SPEC `a` (REWRITE_RULE [INw_def] INw_MODw))
    THEN `1 + MODw a <= 2 EXP WL` by DECIDE_TAC
    THEN RW_TAC arith_ss [EQUIVw_def,ONE_COMP_def,TWO_COMP_def,SUB_RIGHT_SUB,SUB_RIGHT_ADD]
    THEN Cases_on `1 + MODw a = 2 EXP WL`
    THENL [
      RULE_ASSUM_TAC (SIMP_RULE std_ss [GSYM SUC_ONE_ADD,GSYM PRE_SUC_EQ,ZERO_LT_TWOEXP])
        THEN ASM_SIMP_TAC arithr_ss [MODw_def,PRE_SUB1],
      FULL_SIMP_TAC arithr_ss []
    ]
);

(* -------------------------------------------------------- *)

val SUC_SUB = SIMP_CONV arithr_ss [ADD1] ``SUC a - a``;

val NOT_BIT = prove(
  `!n a. ~BIT n a = (BITS n n a = 0)`,
  RW_TAC std_ss [BIT_def,BITS_THM,SUC_SUB,EXP_1,GSYM NOT_MOD2_LEM]
);

val NOT_BITS = prove(
  `!n a. ~(BITS n n a = 0) = (BITS n n a = 1)`,
  RW_TAC std_ss [GSYM NOT_BIT,GSYM BIT_def]
);


val BIT_SLICE = store_thm("BIT_SLICE",
  `!n a b. (BIT n a = BIT n b) = (SLICE n n a = SLICE n n b)`,
  REPEAT STRIP_TAC THEN EQ_TAC
    THENL [
      Cases_on `BIT n a`
        THEN FULL_SIMP_TAC arith_ss [BIT_def,SLICE_THM]
        THEN FULL_SIMP_TAC arith_ss [GSYM NOT_BITS],
      Cases_on `BITS n n a = 1`
        THEN Cases_on `BITS n n b = 1`
        THEN FULL_SIMP_TAC arith_ss [BIT_def,SLICE_THM]
        THEN FULL_SIMP_TAC arith_ss [GSYM NOT_BITS,MULT_CLAUSES,
                                     REWRITE_RULE [GSYM NOT_ZERO_LT_ZERO] ZERO_LT_TWOEXP]
    ]
);

val BITS_COR = GEN_ALL (SIMP_RULE arithr_ss [DIV1] (SPECL [`h`,`0`] BITS2_THM));
val SLICE_COR = GEN_ALL (SIMP_RULE arithr_ss [] (SPECL [`n`,`h`,`0`] SLICE_THM));

val BITS_SUC = store_thm("BITS_SUC",
  `!n a. BITS (SUC n) 0 a = SLICE (SUC n) (SUC n) a + BITS n 0 a`,
  RW_TAC arith_ss [GSYM SLICE_COR,SLICE_COMP_THM]
);

val DECEND_LEMMA = prove(
  `!P y.  (!x. x <= SUC y ==> P x) ==> (!x. x <= y ==> P x)`,
  RW_TAC arith_ss []
);

val SUB_BITS = prove(
  `!n a b. (BITS (SUC n) 0 a = BITS (SUC n) 0 b) ==> (BITS n 0 a = BITS n 0 b)`,
  REPEAT STRIP_TAC
    THEN ONCE_REWRITE_TAC [GSYM (SIMP_RULE arith_ss [] (SPECL [`SUC n`,`0`,`n`,`0`] BITS_COMP_THM))]
    THEN ASM_REWRITE_TAC []
);

val BIT_BITS_THM = store_thm("BIT_BITS_THM",
  `!n a b. (!x. x <= n ==> (BIT x a = BIT x b)) = (BITS n 0 a = BITS n 0 b)`,
  Induct_on `n`
    THEN REPEAT STRIP_TAC
    THENL [
      RW_TAC arith_ss [REWRITE_RULE [SLICE_COR] (SPEC `0` BIT_SLICE)],
      EQ_TAC
        THENL [
          RW_TAC std_ss [BITS_SUC]
            THEN POP_ASSUM (fn th => SIMP_TAC arith_ss [SIMP_RULE arith_ss [BIT_SLICE] (SPEC `SUC n` th)]
                                       THEN ASSUME_TAC th)
            THEN IMP_RES_TAC (BETA_RULE (SPECL [`\x. BIT x a = BIT x b`,`n`] DECEND_LEMMA))
            THEN PROVE_TAC [],
          REPEAT STRIP_TAC
            THEN IMP_RES_TAC SUB_BITS
            THEN FULL_SIMP_TAC arith_ss [BITS_SUC,GSYM BIT_SLICE]
            THEN PAT_ASSUM `!a b.  (!x. x <= n ==> (BIT x a = BIT x b)) = (BITS n 0 a = BITS n 0 b)`
                   (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SYM (SPECL [`a`,`b`] th)]))
            THEN Cases_on `x <= n`
            THEN ASM_SIMP_TAC arith_ss []
            THEN `x = SUC n` by ASM_SIMP_TAC arith_ss []
            THEN ASM_SIMP_TAC arith_ss []
        ]
    ]
);

(* BIT_EQUIV_THM: |- !a b. (!x. x < WL ==> (BIT x a = BIT x b)) = a EQUIVw b *)
val BIT_EQUIV_THM = save_thm("BIT_EQUIV_THM",
   SIMP_RULE std_ss [BITS_COR,GSYM MODw_def,GSYM WL_def,GSYM EQUIVw_def,LESS_EQ_IMP_LESS_SUC,
                REWRITE_RULE [GSYM LESS_EQ,GSYM WL_def] (ONCE_REWRITE_CONV [GSYM LESS_EQ_MONO] ``x <= HB``)]
                    (SPEC `HB` BIT_BITS_THM)
);

(* -------------------------------------------------------- *)

val EXP_EVEN  = prove(
  `!n. 0 < n ==> EVEN (2 EXP n)`,
  RW_TAC std_ss [EVEN_EXISTS]
    THEN EXISTS_TAC `2 EXP PRE n`
    THEN RW_TAC arith_ss [GSYM EXP,SIMP_RULE std_ss [] (SPECL [`PRE n`,`n`] PRE_SUC_EQ)]
);

val TWOEXP_SUB_MOD = prove(
  `!m n. 1 <= 2 EXP n - (a MOD 2 EXP n)`,
  REPEAT STRIP_TAC
    THEN ASSUME_TAC (CONJUNCT2 (SPEC `a` (SIMP_RULE std_ss [ZERO_LT_TWOEXP] (SPEC `2 EXP n` DIVISION))))
    THEN IMP_RES_TAC LESS_ADD_1
    THEN POP_ASSUM (fn th => SUBST_OCCS_TAC [([1],th)])
    THEN SIMP_TAC arith_ss []
);

(* TWOEXP_SUB_MOD2: |- !a n. ~(2 EXP SUC n - 2 * a MOD 2 EXP n < 2) *)
val TWOEXP_SUB_MOD2 =
      let val th = REWRITE_RULE [SYM TWO] (GEN_ALL (SPECL [`m`,`n`,`1`] MULT_LESS_EQ_SUC)) in
          GEN_ALL (REWRITE_RULE [GSYM NOT_LESS,MULT_RIGHT_1,LEFT_SUB_DISTRIB,GSYM EXP]
             (ONCE_REWRITE_RULE [th] (SPEC_ALL TWOEXP_SUB_MOD)))
      end;

val BITWISE_ONE_COMP_LEM = prove(
  `!n a b. BITWISE n (\x y. ~x) a b = 2 EXP n - 1 - a MOD 2 EXP n`,
  let val th1 = GSYM (ONCE_REWRITE_RULE [MULT_COMM] (
                SIMP_RULE arithr_ss [SLICE_THM,DIV1,BITS_THM] 
                         (SPECL [`n`,`0`,`0`,`a`] SLICE_COMP_THM))) 
  in
  Induct_on `n`
    THEN REPEAT STRIP_TAC
    THENL [
      SIMP_TAC arith_ss [BITWISE_def,EXP,REWRITE_RULE [SYM ONE] MOD_ONE],
      Cases_on `n = 0`
        THENL [RW_TAC arith_ss [BITWISE_def,EXP,
                        REWRITE_RULE [SYM ONE] MOD_ONE,LSB_ODD,ODD_MOD2_LEM]
               THEN POP_ASSUM (fn th => SIMP_TAC arith_ss 
                                 [REWRITE_RULE [GSYM NOT_MOD2_LEM] th]),
          RW_TAC std_ss [BITWISE_def,LSB_ODD,ODD_MOD2_LEM] THEN 
          RW_TAC arith_ss [GSYM (CONJUNCT2 EXP)]
            THEN `SUC 0 <= n` by ASM_SIMP_TAC arith_ss []
            THENL [
               RULE_ASSUM_TAC (REWRITE_RULE [GSYM NOT_MOD2_LEM])
                 THEN ASM_SIMP_TAC arith_ss [th1]
                 THEN SIMP_TAC std_ss [SUB_PLUS]
                 THEN REPEAT (WEAKEN_TAC (K true))
                 THEN Cases_on `2 EXP SUC n - 2 * (a DIV 2) MOD 2 EXP n = 2`
                 THENL [
                   ASM_SIMP_TAC arithr_ss [],
                   ASSUME_TAC (SPECL [`n`,`a DIV 2`] TWOEXP_SUB_MOD2)
                     THEN IMP_RES_TAC LESS_CASES_IMP
                     THEN POP_ASSUM (fn th => 
                            ASSUME_TAC (REWRITE_RULE [GSYM NOT_LESS_EQUAL] th))
                     THEN ONCE_REWRITE_TAC [SUB_RIGHT_ADD]
                     THEN ASM_SIMP_TAC std_ss [GSYM SUB_SUB,
                              REDUCE_CONV ``2 - 1``,DECIDE ``1 <= 2``] 
                 ],
               RULE_ASSUM_TAC (SIMP_RULE std_ss [])
                 THEN ASM_SIMP_TAC arith_ss [th1]
            ]
        ]
    ]
  end
);

val BITWISE_ONE_COMP_THM = store_thm("BITWISE_ONE_COMP_THM",
  `!a b. BITWISE WL (\x y. ~x) a b = ONE_COMP a`,
  RW_TAC std_ss [SPEC `WL` BITWISE_ONE_COMP_LEM,ONE_COMP_def,MODw_def]
);

val ONE_COMP_THM = store_thm("ONE_COMP_THM",
  `!a x. x < WL ==> (BIT x (ONE_COMP a) = ~BIT x a)`,
  REWRITE_TAC [GSYM BITWISE_ONE_COMP_THM] THEN RW_TAC std_ss [BITWISE_THM]
);

val ZERO_IS_FALSE = prove(
  `!x. ~BIT x 0`,
  RW_TAC arith_ss [BIT_def,BITS_THM,ZERO_LT_TWOEXP,ZERO_DIV,ZERO_MOD]
);

(* ONE_COMP_TRUE: |- !x. x < WL ==> BIT x (ONE_COMP 0) *)
val ONE_COMP_TRUE = REWRITE_RULE [ZERO_IS_FALSE] (SPEC `0` ONE_COMP_THM);

(* -------------------------------------------------------- *)

val OR_def = Define`OR = BITWISE WL $\/`;
val AND_def = Define`AND = BITWISE WL $/\`;
val EOR_def = Define`EOR = BITWISE WL (\x y. ~(x = y))`;
val ATRUE_def = Define`ATRUE = ONE_COMP 0`;

(* -------------------------------------------------------- *)

val BITWISE_THM2 = save_thm("BITWISE_THM2",
  (GEN `y` o GEN `op` o GEN `a` o GEN `b`)
  (SIMP_RULE std_ss [BITWISE_THM] (SPECL [`BITWISE WL op a b`,`y`] BIT_EQUIV_THM))
);

val OR_ASSOC_QT = save_thm("OR_ASSOC_QT",
  (GEN `a` o GEN `b` o GEN `c`)
  (SIMP_RULE std_ss [BITWISE_THM,DISJ_ASSOC,GSYM OR_def]
  (SPECL [`BITWISE WL $\/ (BITWISE WL $\/ a b) c`,`$\/`,`a`,`BITWISE WL $\/ b c`] BITWISE_THM2))
);

val OR_COMM_QT = save_thm("OR_COMM_QT",
  (GEN `a` o GEN `b`)
  (SIMP_RULE std_ss [BITWISE_THM,DISJ_COMM,GSYM OR_def]
  (SPECL [`BITWISE WL ($\/) b a`,`$\/`,`a`,`b`] BITWISE_THM2))
);

val OR_ABSORB_QT = save_thm("OR_ABSORB_QT",
  (GEN `a` o GEN `b`)
  (SIMP_RULE std_ss [BITWISE_THM,PROVE [] `!a b. a /\ (a \/ b) = a`,GSYM OR_def,GSYM AND_def]
  (SPECL [`a`,`$/\`,`a`,`BITWISE WL $\/ a b`] BITWISE_THM2))
);

val OR_IDEM_QT = save_thm("OR_IDEM_QT",
  GEN_ALL (SIMP_RULE std_ss [OR_CLAUSES,GSYM OR_def] (SPECL [`a`,`$\/`,`a`,`a`] BITWISE_THM2))
);

val AND_ASSOC_QT = save_thm("AND_ASSOC_QT",
  (GEN `a` o GEN `b` o GEN `c`)
  (SIMP_RULE std_ss [BITWISE_THM,CONJ_ASSOC,GSYM AND_def]
  (SPECL [`BITWISE WL $/\ (BITWISE WL $/\ a b) c`,`$/\`,`a`,`BITWISE WL $/\ b c`] BITWISE_THM2))
);

val AND_COMM_QT = save_thm("AND_COMM_QT",
  (GEN `a` o GEN `b`)
  (SIMP_RULE std_ss [BITWISE_THM,CONJ_COMM,GSYM AND_def]
  (SPECL [`BITWISE WL $/\ b a`,`$/\`,`a`,`b`] BITWISE_THM2))
);

val AND_ABSORB_QT = save_thm("AND_ABSORB_QT",
  (GEN `a` o GEN `b`)
  (SIMP_RULE std_ss [BITWISE_THM,PROVE [] `!a b. a \/ (a /\ b) = a`,GSYM AND_def,GSYM OR_def]
  (SPECL [`a`,`$\/`,`a`,`BITWISE WL $/\ a b`] BITWISE_THM2))
);

val AND_IDEM_QT = save_thm("AND_IDEM_QT",
  GEN_ALL (SIMP_RULE std_ss [AND_CLAUSES,GSYM AND_def] (SPECL [`a`,`$/\`,`a`,`a`] BITWISE_THM2))
);

val OR_COMP_QT = save_thm("OR_COMP_QT",
  GEN_ALL (SIMP_RULE std_ss [EXCLUDED_MIDDLE,ONE_COMP_TRUE,ONE_COMP_THM,GSYM OR_def,GSYM ATRUE_def]
          (SPECL [`ONE_COMP 0`,`$\/`,`a`,`ONE_COMP a`] BITWISE_THM2))
);

val AND_COMP_QT = save_thm("AND_COMP_QT",
  GEN_ALL (SIMP_RULE std_ss [ONE_COMP_THM,ZERO_IS_FALSE,GSYM AND_def]
          (SPECL [`0`,`$/\`,`a`,`ONE_COMP a`] BITWISE_THM2))
);

val ONE_COMP_QT = save_thm("ONE_COMP_QT",
  GEN_ALL (SIMP_RULE std_ss [BITWISE_ONE_COMP_THM,ONE_COMP_THM]
          (SPECL [`a`,`\x y. ~x`,`ONE_COMP a`,`b`] BITWISE_THM2))
);

val RIGHT_AND_OVER_OR_QT = save_thm("RIGHT_AND_OVER_OR_QT",
  (GEN `a` o GEN `b` o GEN `c`)
  (SIMP_RULE std_ss [BITWISE_THM,RIGHT_AND_OVER_OR,GSYM AND_def,GSYM OR_def]
  (SPECL [`BITWISE WL $\/ (BITWISE WL $/\ a c) (BITWISE WL $/\ b c)`,
          `$/\`,`BITWISE WL $\/ a b`,`c`] BITWISE_THM2))
);

val RIGHT_OR_OVER_AND_QT = save_thm("RIGHT_OR_OVER_AND_QT",
  (GEN `a` o GEN `b` o GEN `c`)
  (SIMP_RULE std_ss [BITWISE_THM,RIGHT_OR_OVER_AND,GSYM AND_def,GSYM OR_def]
  (SPECL [`BITWISE WL $/\ (BITWISE WL $\/ a c) (BITWISE WL $\/ b c)`,
          `$\/`,`BITWISE WL $/\ a b`,`c`] BITWISE_THM2))
);

val DE_MORGAN_THM_QT1 = 
  (SIMP_RULE std_ss [BITWISE_THM,BITWISE_ONE_COMP_THM,ONE_COMP_THM,GSYM AND_def,GSYM OR_def]
  (SPECL [`ONE_COMP (BITWISE WL $/\ a b)`,
          `$\/`,`ONE_COMP a`,`ONE_COMP b`] BITWISE_THM2));

val DE_MORGAN_THM_QT2 = 
  (SIMP_RULE std_ss [BITWISE_THM,BITWISE_ONE_COMP_THM,ONE_COMP_THM,GSYM AND_def,GSYM OR_def]
  (SPECL [`ONE_COMP (BITWISE WL $\/ a b)`,
          `$/\`,`ONE_COMP a`,`ONE_COMP b`] BITWISE_THM2));

val DE_MORGAN_THM_QT = save_thm("DE_MORGAN_THM_QT",
  (GEN `a` o GEN `b`)
  (CONJ (ONCE_REWRITE_RULE [EQUIVw_SYM] DE_MORGAN_THM_QT1)
        (ONCE_REWRITE_RULE [EQUIVw_SYM] DE_MORGAN_THM_QT2))
);

(* -------------------------------------------------------- *)

val BIT_EQUIV = store_thm("BIT_EQUIV",
  `!n a b. n < WL ==> a EQUIVw b ==> (BIT n a = BIT n b)`,
  RW_TAC std_ss [GSYM BIT_EQUIV_THM]
);

(* -------------------------------------------------------- *)

val HB_LESS_WL = REWRITE_RULE [SYM WL_def] (SPEC `HB` LESS_SUC_REFL);

val LSB_WELLDEF = store_thm("LSB_WELLDEF",
  `!a b. a EQUIVw b ==> (LSB a = LSB b)`,
  RW_TAC std_ss [WL_POS,REDUCE_RULE (SPEC `0` BIT_EQUIV),LSB_def]
);

val MSB_WELLDEF = store_thm("MSB_WELLDEF",
  `!a b. a EQUIVw b ==> (MSB a = MSB b)`,
  RW_TAC std_ss [HB_LESS_WL,REDUCE_RULE (SPEC `HB` BIT_EQUIV),MSB_def]
);

(* -------------------------------------------------------- *)

val BIT_SET_NOT_ZERO = prove(
  `!a. (a MOD 2 = 1) ==> (1 <= a)`,
  SPOSE_NOT_THEN STRIP_ASSUME_TAC
    THEN `a = 0` by DECIDE_TAC
    THEN FULL_SIMP_TAC arith_ss [ZERO_MOD]
);

val BIT_SET_NOT_ZERO_COR = prove(
  `!x n op a b. x < n ==> op (BIT x a) (BIT x b) ==> (1 <= (BITWISE n op a b DIV 2 EXP x))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss [BITWISE_COR,BIT_SET_NOT_ZERO]
);

val BITWISE_COR0 = REWRITE_RULE [GSYM LESS_EQ,ONE,EXP_1] (SPEC `1` BITWISE_NOT_COR);
val BITWISE_COR1 = REWRITE_RULE [GSYM LESS_EQ,ONE,EXP_1] (SPEC `1` BITWISE_COR);
val BITWISE_COR2 = SIMP_RULE arith_ss [GSYM LESS_EQ,DIV1,EXP] (SPEC `0` BITWISE_NOT_COR);
val BITWISE_COR3 = SIMP_RULE arith_ss [GSYM LESS_EQ,DIV1,EXP] (SPEC `0` BITWISE_COR);
val BIT_SET_NOT_ZERO_COR1 = REWRITE_RULE [GSYM LESS_EQ,REWRITE_RULE [ONE] EXP_1]
                                         (SPEC `SUC 0` BIT_SET_NOT_ZERO_COR);
val BIT_SET_NOT_ZERO_COR2 = REWRITE_RULE [DIV1,EXP] (SPEC `0` BIT_SET_NOT_ZERO_COR);
val MULT_DIV2 = ONCE_REWRITE_RULE [MULT_COMM] (SIMP_RULE arithr_ss [] (SPEC `2` MULT_DIV));

val ADD2_EXP = prove(
  `!n p. (n = p + 2) ==> (2 EXP n = 2 * (2 * 2 EXP p))`,
  RW_TAC arithr_ss [EXP_ADD]
);

val REARRANGE = prove(
  `!a b c. b <= a ==> (((a - b) + c) + b = (c + a))`,
  REPEAT STRIP_TAC
    THEN ONCE_REWRITE_TAC [GSYM ADD_ASSOC]
    THEN ONCE_REWRITE_TAC [ADD_COMM]
    THEN ONCE_REWRITE_TAC [GSYM ADD_ASSOC]
    THEN REWRITE_TAC [SPECL [`b`,`a - b`] ADD_COMM]
    THEN ASM_SIMP_TAC arith_ss [SUB_ADD]
);

val REARRANGE2 = prove(`!a b c. a + (b + c) = (a + c) + b`,RW_TAC arith_ss []);

val something = prove(
  `!n. 1 < n ==> (2 EXP (n - 1) = 2 EXP n DIV 2)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_ADD
    THEN POP_ASSUM (fn th => SIMP_TAC arith_ss [SYM th,EXP_ADD,EXP_1,MULT_DIV])
);

val something = REWRITE_RULE [ONE] something;

val BITWISE_ISTEP = store_thm("BITWISE_ISTEP",
  `!n op a b. 0 < n ==> (BITWISE n op (a DIV 2) (b DIV 2) =
                        (BITWISE n op a b) DIV 2 + SET (op (BIT n a) (BIT n b)) (n - 1))`,
  Induct_on `n`
    THEN REPEAT STRIP_TAC
    THENL [
       FULL_SIMP_TAC arith_ss [],
       Cases_on `1 < n`
         THENL [
           FULL_SIMP_TAC arith_ss []
             THEN IMP_RES_TAC LESS_ADD_1
             THEN RULE_ASSUM_TAC (SIMP_RULE arith_ss [])
             THEN POP_ASSUM (fn th => ASSUME_TAC (MATCH_MP ADD2_EXP th))
             THEN RULE_ASSUM_TAC (SIMP_RULE std_ss [ONE])
             THEN RW_TAC arithr_ss [BITWISE_def,LSB_def,BIT_DIV2,SET_def,something,
                                    ADD_DIV_ADD_DIV3,MULT_DIV2]
             THEN ASM_SIMP_TAC std_ss [ADD_DIV_ADD_DIV3,MULT_DIV2,LEFT_ADD_DISTRIB]
             THEN ASM_SIMP_TAC std_ss [MULT_DIV2,SYM ONE,EXP,DIV_MULT_THM2,BITWISE_COR0,BITWISE_COR1]
             THEN IMP_RES_TAC BIT_SET_NOT_ZERO_COR1
             THEN SIMP_TAC std_ss [REARRANGE2]
             THEN ASM_SIMP_TAC arith_ss [REARRANGE],
           `(n = 0) \/ (n = 1)` by ASM_SIMP_TAC arith_ss []
             THEN RW_TAC arithr_ss [ONE,SET_def,BITWISE_def,LSB_def,BIT_DIV2]
         ]
    ]
);

val BITWISE_ISTEP2 = store_thm("BITWISE_ISTEP2",
 `!n op a b. n <= WL ==> (BITWISE n op a c EQUIVw BITWISE n op b d =
                         (BITWISE n op a c = BITWISE n op b d))`,
  REPEAT STRIP_TAC
    THEN POP_ASSUM (fn th => ASSUME_TAC (MATCH_MP TWOEXP_MONO2 th))
    THEN ASSUME_TAC (SPECL [`n`,`op`,`a`,`c`] BITWISE_LT_2EXP)
    THEN ASSUME_TAC (SPECL [`n`,`op`,`b`,`d`] BITWISE_LT_2EXP)
    THEN IMP_RES_TAC LESS_LESS_EQ_TRANS
    THEN ASM_SIMP_TAC std_ss [EQUIVw_def,MODw_def,LESS_MOD]
);

val SAME_OP = prove(
  `!op a b c d. (BIT 0 c = BIT 0 d) /\ (BIT 0 a = BIT 0 b) /\
                op (BIT 0 b) (BIT 0 d) ==> op (BIT 0 a) (BIT 0 c)`,
  RW_TAC std_ss []
);

val SAME_OP2 = prove(
  `!op a b c d. (BIT 0 c = BIT 0 d) /\ (BIT 0 a = BIT 0 b) /\
                ~(op (BIT 0 b) (BIT 0 d)) ==> ~(op (BIT 0 a) (BIT 0 c))`,
  RW_TAC std_ss []
);

val SPEC_MOD_TIMES2 = prove(
  `!p. 2 * (2 EXP (p + WL)) = (2 * 2 EXP p) * 2 EXP WL`,
  RW_TAC arith_ss [EXP_ADD,MULT_ASSOC]
);

val DIV_TIMES = prove(
  `!n. 0 < n ==> (2 * (2 EXP n DIV 2) = 2 EXP n)`,
  RW_TAC arith_ss [DIV_MULT_THM2,SIMP_RULE std_ss [EVEN_MOD2_LEM] (SPEC `n` EXP_EVEN)]
);

val SPEC_DIV_TIMES = SIMP_RULE std_ss [WL_POS] (SPEC `WL` DIV_TIMES);

val something2 = REWRITE_RULE [GSYM WL_def,GSYM ADD1] (SIMP_CONV arith_ss [WL_def,ADD1] ``SUC (WL - 1)``);

val BITWISE_WELLDEF = store_thm("BITWISE_WELLDEF",
  `!n op a b c d. a EQUIVw b /\ c EQUIVw d ==> (BITWISE n op) a c EQUIVw (BITWISE n op) b d`,
  let val tac = Cases_on `n <= WL`
        THENL [
          `BITWISE n op a c EQUIVw BITWISE n op b d` by PROVE_TAC []
            THEN `BITWISE n op a c = BITWISE n op b d` by IMP_RES_TAC BITWISE_ISTEP2
            THEN ASM_SIMP_TAC std_ss []
            THEN Cases_on `n = WL`
            THENL [
               RW_TAC arith_ss [SET_def,something2,
                  MULT_CLAUSES,GSYM EXP,MODw_def,SPEC_MOD_TIMES,SPEC_DIV_TIMES],
               `n < WL` by ASM_SIMP_TAC arith_ss []
                  THEN IMP_RES_TAC BIT_EQUIV
                  THEN ASM_SIMP_TAC std_ss []
            ],
          RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS_EQUAL])
            THEN IMP_RES_TAC LESS_ADD_1
            THEN POP_ASSUM (K ALL_TAC)
            THEN RW_TAC arith_ss [ADD_CLAUSES,MULT_CLAUSES,MODw_def,SET_def,
                                ONCE_REWRITE_RULE [ADD_COMM] MOD_TIMES,
                                MOD_TIMES,SPEC_MOD_TIMES2,ZERO_LT_TWOEXP]
            THEN RULE_ASSUM_TAC (SIMP_RULE arith_ss [EQUIVw_def,MODw_def])
            THEN FULL_SIMP_TAC std_ss []
        ] in
  Induct_on `n`
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC LSB_WELLDEF
    THEN NTAC 4 (WEAKEN_TAC (K true))
    THEN SIMP_TAC arith_ss [BITWISE_def,EQUIVw_def]
    THEN Cases_on `n = 0`
    THENL [
      ASM_SIMP_TAC arith_ss [BITWISE_def,EQUIVw_def],
      RULE_ASSUM_TAC (REWRITE_RULE [NOT_ZERO_LT_ZERO])
        THEN FULL_SIMP_TAC std_ss [LSB_def,BITWISE_ISTEP,LEFT_ADD_DISTRIB,DIV_MULT_THM2]
        THEN RW_TAC std_ss [BITWISE_COR2,BITWISE_COR3,SUB_0]
        THENL [
           `op (BIT 0 a) (BIT 0 c)` by IMP_RES_TAC SAME_OP
             THEN IMP_RES_TAC BIT_SET_NOT_ZERO_COR2
             THEN NTAC 2 (POP_ASSUM (K ALL_TAC))
             THEN SIMP_TAC std_ss [REARRANGE2]
             THEN ASM_SIMP_TAC arith_ss [REARRANGE]
             THEN tac,
           `~(op (BIT 0 a) (BIT 0 c))` by IMP_RES_TAC SAME_OP2
             THEN tac
        ]
    ]
  end
);

val BITWISEw_WELLDEF = save_thm("BITWISEw_WELLDEF",SPEC `WL` BITWISE_WELLDEF);

val OR_WELLDEF = REWRITE_RULE [GSYM OR_def] (SPEC `$\/` BITWISEw_WELLDEF);
val AND_WELLDEF = REWRITE_RULE [GSYM AND_def] (SPEC `$/\` BITWISEw_WELLDEF);
val EOR_WELLDEF = REWRITE_RULE [GSYM EOR_def] (SPEC `(\x y. ~(x = y))` BITWISEw_WELLDEF);

(* -------------------------------------------------------- *)

(*
val BITWISE_IDEM = prove(
  `!n op a b. n <= WL ==> INw (BITWISE n op a b)`,
  RW_TAC std_ss [INw_def]
    THEN POP_ASSUM (fn th => ASSUME_TAC (MATCH_MP TWOEXP_MONO2 th))
    THEN ASSUME_TAC (SPEC_ALL BITWISE_LT_2EXP)
    THEN IMP_RES_TAC LESS_LESS_EQ_TRANS
);

val BITWISE_IDEM2 = prove(
  `!n op a b. n <= WL ==> (MODw (BITWISE n op a b) = BITWISE n op a b)`,
  RW_TAC std_ss [BITWISE_IDEM,TOw_IDEM]
);

val SPEC_MOD_TIMES2 = prove(
  `!p n r. (n = WL + (p + 1)) ==> (MODw (2 EXP n + r) = MODw r)`,
  RW_TAC std_ss [MODw_def,EXP_ADD,ZERO_LT_TWOEXP,ONCE_REWRITE_RULE [MULT_COMM] MOD_TIMES]
);

val BITWISE_CHOP = prove(
  `!n op a b. ~(n <= WL) ==> (BITWISE n op a b EQUIVw BITWISE WL op a b)`,
  REWRITE_TAC [NOT_LESS_EQUAL]
    THEN Induct_on `n`
    THEN REPEAT STRIP_TAC
    THENL [
       FULL_SIMP_TAC arithr_ss [],
       Cases_on `WL < n`
         THENL [
           FULL_SIMP_TAC std_ss [EQUIVw_def]
             THEN `0 < n` by ASM_SIMP_TAC arithr_ss [WL_POS,LESS_TRANS]
             THEN RW_TAC arith_ss [BITWISE_def,LSB_def,BITWISE_ISTEP,SET_def,DIV_TIMES]
             THEN IMP_RES_TAC BIT_SET_NOT_ZERO_COR2
             THEN ASM_SIMP_TAC arith_ss [DIV_MULT_THM2,REARRANGE,BITWISE_COR2,BITWISE_COR3]
             THEN IMP_RES_TAC (SPECL [`n`,`WL`] LESS_ADD_1)
             THEN PAT_ASSUM `n = WL + (p + 1)`
                    (fn th => SIMP_TAC std_ss [MATCH_MP SPEC_MOD_TIMES2 th,EQUIVw_def])
             THEN FULL_SIMP_TAC std_ss [],
           `n = WL` by ASM_SIMP_TAC arithr_ss []
             THEN POP_ASSUM_LIST (fn thl => ASSUME_TAC (hd thl))
             THEN `0 < n` by ASM_SIMP_TAC std_ss [WL_POS]
             THEN RW_TAC arith_ss [BITWISE_def,LSB_def,BITWISE_ISTEP,SET_def,SPEC_DIV_TIMES]
             THEN IMP_RES_TAC BIT_SET_NOT_ZERO_COR2
             THEN ASM_SIMP_TAC arith_ss [DIV_MULT_THM2,REARRANGE,BITWISE_COR2,BITWISE_COR3,
                                         MODw_def,SPEC_MOD_TIMES,EQUIVw_def]
         ]
    ]
);

(* BITWISE_CHOP2: |- !n op a b. ~(n <= WL) ==> (MODw (BITWISE n op a b) = BITWISE WL op a b) *)
val BITWISE_CHOP2 = REWRITE_RULE [EQUIVw_def,SIMP_RULE arith_ss [] (SPEC `WL` BITWISE_IDEM2)] BITWISE_CHOP;
*)

(* -------------------------------------------------------- *)

val SUC_WELLDEF = store_thm("SUC_WELLDEF",
  `!a b. a EQUIVw b ==> SUC a EQUIVw SUC b`,
  RW_TAC std_ss [EQUIVw_def,ADD1]
    THEN ONCE_REWRITE_TAC [MOD_ADD]
    THEN ASM_REWRITE_TAC []
);

val ADD_WELLDEF = store_thm("ADD_WELLDEF",
  `!a b c d. a EQUIVw b /\ c EQUIVw d ==> a + c EQUIVw b + d`,
  RW_TAC std_ss [EQUIVw_def]
    THEN ONCE_REWRITE_TAC [MOD_ADD]
    THEN ASM_REWRITE_TAC []
);

val MUL_WELLDEF_LEM = store_thm("MUL_WELLDEF_LEM",
  `!a b. (MODw a = 0) ==> (MODw (a * b) = 0)`,
  Induct_on `b`
    THENL [
      RW_TAC std_ss [MODw_def,MULT_CLAUSES,ZERO_LT_TWOEXP,ZERO_MOD],
      RW_TAC std_ss [MULT_CLAUSES]
        THEN ONCE_REWRITE_TAC [MOD_ADD]
        THEN FULL_SIMP_TAC std_ss []
        THEN SIMP_TAC arith_ss [MODw_def,ZERO_LT_TWOEXP,ZERO_MOD]
    ]
);

val MUL_WELLDEF_LEM2 = store_thm("MUL_WELLDEF_LEM2",
  `!b. (MODw 0 = MODw b) ==> (MODw b = 0)`,
  RW_TAC std_ss [MODw_def,ZERO_LT_TWOEXP,ZERO_MOD]
);

val MUL_WELLDEF = store_thm("MUL_WELLDEF",
  `!a b c d. a EQUIVw b /\ c EQUIVw d ==> a * c EQUIVw b * d`,
  REWRITE_TAC [EQUIVw_def]
    THEN Induct_on `a`
    THEN REPEAT STRIP_TAC
    THENL [
      SIMP_TAC std_ss [MULT_CLAUSES]
        THEN IMP_RES_TAC MUL_WELLDEF_LEM2
        THEN ASM_SIMP_TAC std_ss [MUL_WELLDEF_LEM],
      SIMP_TAC std_ss [MULT_CLAUSES]
        THEN IMP_RES_TAC (REWRITE_RULE [EQUIVw_def] SUC_EQUIV_COMP)
        THEN `MODw (a * c) = MODw ((b + (2 EXP WL - 1)) * d)` by PROVE_TAC []
        THEN ONCE_REWRITE_TAC [MOD_ADD]
        THEN ASM_SIMP_TAC std_ss []
        THEN POP_ASSUM_LIST (K ALL_TAC)
        THEN SIMP_TAC std_ss [RIGHT_ADD_DISTRIB,RIGHT_SUB_DISTRIB,MULT_CLAUSES,GSYM MOD_ADD]
        THEN ONCE_REWRITE_TAC [GSYM ADD_ASSOC]
        THEN SIMP_TAC std_ss [SUB_ADD,SIMP_RULE std_ss [exp_gteq,MULT_CLAUSES]
                                                       (SPECL [`1`,`2 EXP WL`] LESS_MONO_MULT)]
        THEN ONCE_REWRITE_TAC [ADD_COMM]
        THEN ONCE_REWRITE_TAC [MULT_COMM]
        THEN SIMP_TAC std_ss [MODw_def,ZERO_LT_TWOEXP,MOD_TIMES]
    ]
);

(* MODw_MULT = |- !b a. MODw (a * b) = MODw (MODw a * MODw b) *)
val MODw_MULT = save_thm("MODw_MULT",
  GEN_ALL (SIMP_RULE std_ss [EQUIVw_def,MODw_IDEM2] (SPECL [`a`,`MODw a`,`b`,`MODw b`] MUL_WELLDEF))
);

val ONE_COMP_WELLDEF = store_thm("ONE_COMP_WELLDEF",
  `!a b. a EQUIVw b ==> ONE_COMP a EQUIVw ONE_COMP b`,
  RW_TAC std_ss [EQUIVw_def,ONE_COMP_def]
);

val TWO_COMP_WELLDEF = store_thm("TWO_COMP_WELLDEF",
  `!a b. a EQUIVw b ==> TWO_COMP a EQUIVw TWO_COMP b`,
  RW_TAC std_ss [EQUIVw_def,TWO_COMP_def]
);

val TOw_WELLDEF = store_thm("TOw_WELLDEF",
  `!a b. a EQUIVw b ==> MODw a EQUIVw MODw b`,
  RW_TAC std_ss [EQUIVw_def]
);

(* -------------------------------------------------------- *)

val LSR_ONE_def = Define`LSR_ONE a = MODw a DIV 2`;
val ASR_ONE_def = Define`ASR_ONE a = LSR_ONE a + SET (MSB a) HB`;
val ROR_ONE_def = Define`ROR_ONE a = LSR_ONE a + SET (LSB a) HB`;
val RRXn_def = Define`RRXn c a = LSR_ONE a + SET c HB`;

val LSR_ONE_WELLDEF = store_thm("LSR_ONE_WELLDEF",
  `!a b. a EQUIVw b ==> LSR_ONE a EQUIVw LSR_ONE b`,
  RW_TAC std_ss [EQUIVw_def,LSR_ONE_def]
);

val ASR_ONE_WELLDEF = store_thm("ASR_ONE_WELLDEF",
  `!a b. a EQUIVw b ==> ASR_ONE a EQUIVw ASR_ONE b`,
  RW_TAC std_ss [EQUIVw_def,ASR_ONE_def,LSR_ONE_def]
    THEN IMP_RES_TAC (REWRITE_RULE [EQUIVw_def] MSB_WELLDEF)
    THEN ASM_SIMP_TAC std_ss []
);

val ROR_ONE_WELLDEF = store_thm("ROR_ONE_WELLDEF",
  `!a b. a EQUIVw b ==> ROR_ONE a EQUIVw ROR_ONE b`,
  RW_TAC std_ss [EQUIVw_def,ROR_ONE_def,LSR_ONE_def]
    THEN IMP_RES_TAC (REWRITE_RULE [EQUIVw_def] LSB_WELLDEF)
    THEN ASM_SIMP_TAC std_ss []
);

val RRX_WELLDEF = store_thm("RRX_WELLDEF",
  `!a b c. a EQUIVw b ==> (RRXn c) a EQUIVw (RRXn c) b`,
  RW_TAC std_ss [EQUIVw_def,RRXn_def,LSR_ONE_def]
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
     AND_ABSORBw,AND_COMPw, ONE_COMPw,RIGHT_AND_OVER_ORw,RIGHT_OR_OVER_ANDw,
     DE_MORGAN_THMw] 
 = 
 define_equivalence_type
   {name = "word",
    equiv = EQUIVw_QT,
    defs = [r("w_0_def",Prefix,"w_0",``0``),
            r("w_1_def",Prefix,"w_1",``AONE``),
            r("w_T_def",Prefix,"w_T",``ATRUE``),
            r("SUCw_def",Prefix,"SUCw",``SUC``),
            r("ADDw_def",Infixl 500,"ADDw",``$+``),
            r("MULw_def",Infixl 550,"MULw",``$*``),
            r("ONE_COMPw_def",Prefix,"ONE_COMPw",``ONE_COMP``),
            r("TWO_COMPw_def",Prefix,"TWO_COMPw",``TWO_COMP``),
            r("LSR_ONEw_def",Prefix,"LSR_ONEw",``LSR_ONE``),
            r("ASR_ONEw_def",Prefix,"ASR_ONEw",``ASR_ONE``),
            r("ROR_ONEw_def",Prefix,"ROR_ONEw",``ROR_ONE``),
            r("RRXw_def",Prefix,"RRXw",``RRXn``),
            r("LSBw_def",Prefix,"LSBw",``LSB``),
            r("MSBw_def",Prefix,"MSBw",``MSB``),
            r("ORw_def",Infixl 600,"ORw",``OR``),
            r("EORw_def",Infixl 600,"EORw",``EOR``),
            r("ANDw_def",Infixl 650,"ANDw",``AND``),
            r("TOw_def",Prefix,"TOw",``MODw``)],
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

val wn_def = Define `wn n = mk_word ($EQUIVw n)`;
val NUMw_def = Define`NUMw w = MODw ($@ (dest_word w))`;

val word_tybij = fetch "-" "word_tybij";
val mk_word_one_one = BETA_RULE (prove_abs_fn_one_one (word_tybij));

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
 
val w_0 = save_thm("w_0",REWRITE_RULE [GSYM wn_def] (definition "w_0_def"));
val w_1 = save_thm("w_1",REWRITE_RULE [GSYM wn_def,AONE_def] (definition "w_1_def"));
val w_T = save_thm("w_T",SIMP_RULE arithr_ss [GSYM wn_def,ATRUE_def,ONE_COMP_def,MODw_def,THE_WL] (definition "w_T_def"));

val ADD_TWO_COMP = save_thm("ADD_TWO_COMP",REWRITE_RULE [TOw_ELIM] ADD_TWO_COMP);
val ADD_TWO_COMP2 = save_thm("ADD_TWO_COMP2",ONCE_REWRITE_RULE [ADD_COMMw] ADD_TWO_COMP);

val ADDw_def = definition "ADDw_def";
val MULw_def = definition "MULw_def";
val ONE_COMPw_def = definition "ONE_COMPw_def";
val TWO_COMPw_def = definition "TWO_COMPw_def";
val LSR_ONEw_def = definition "LSR_ONEw_def";
val ASR_ONEw_def = definition "ASR_ONEw_def";
val ROR_ONEw_def = definition "ROR_ONEw_def";
val RRXw_def = definition "RRXw_def";
val LSBw_def = definition "LSBw_def";
val MSBw_def = definition "MSBw_def";
val ORw_def = definition "ORw_def";
val ANDw_def = definition "ANDw_def";
val EORw_def = definition "EORw_def";

(* -------------------------------------------------------- *)

val SUBw_def = 
  new_infixl_definition 
   ("SUBw_def",`a SUBw b = a ADDw (TWO_COMPw b)`,500);
val LSLw_def = Define`LSLw n x = x MULw wn (2 EXP n)`;
val LSRw_def = Define`LSRw n a = FUNPOW LSR_ONEw n a`;
val ASRw_def = Define`ASRw n a = FUNPOW ASR_ONEw n a`;
val RORw_def = Define`RORw n a = FUNPOW ROR_ONEw n a`;

val BITw_def = Define`BITw b n = BIT b (NUMw n)`;
val BITSw_def = Define`BITSw h l n = BITS h l (NUMw n)`;
val SLICEw_def = Define`SLICEw h l n = SLICE h l (NUMw n)`;
 
(* -------------------------------------------------------- *)

val ssd = SIMPSET {ac = [(SPEC_ALL ADD_ASSOCw, SPEC_ALL ADD_COMMw)],
                congs = [], convs = [], dprocs = [], filter = NONE, rewrs = []};

val word_ss = std_ss++ssd;

val TWO_COMP_ADD = store_thm("TWO_COMP_ADD",
  `!a b. TWO_COMPw (a ADDw b) = TWO_COMPw a ADDw TWO_COMPw b`,
  let val rearrange = EQT_ELIM (SIMP_CONV word_ss []
                         ``TWO_COMPw a ADDw a ADDw (TWO_COMPw b ADDw b) =
                           TWO_COMPw a ADDw TWO_COMPw b ADDw (a ADDw b)``) in
   REPEAT STRIP_TAC
     THEN `TWO_COMPw a ADDw a ADDw (TWO_COMPw b ADDw b) = w_0`
       by REWRITE_TAC [ADD_TWO_COMP2,ADD_CLAUSESw]
     THEN RULE_ASSUM_TAC (REWRITE_RULE [rearrange])
     THEN ASSUME_TAC (SYM (SPEC `a ADDw b` ADD_TWO_COMP2))
     THEN FULL_SIMP_TAC std_ss [EQ_ADD_RCANCELw]
  end
);

val TWO_COMP_ELIM = store_thm("TWO_COMP_ELIM",
  `!a. TWO_COMPw (TWO_COMPw a) = a`,
  STRIP_TAC
    THEN `TWO_COMPw (TWO_COMPw a) ADDw TWO_COMPw a =
          a ADDw TWO_COMPw a` by SIMP_TAC word_ss [ADD_TWO_COMP]
    THEN IMP_RES_TAC EQ_ADD_RCANCELw
);

val ADD_SUB_ASSOC = store_thm("ADD_SUB_ASSOC",
  `!a b c. (a ADDw b SUBw c = a ADDw (b SUBw c))`,
  RW_TAC word_ss [SUBw_def]
);

val ADD_SUB_SYM = store_thm("ADD_SUB_SYM",
  `!a b c. a ADDw b SUBw c = a SUBw c ADDw b`,
  RW_TAC word_ss [SUBw_def]
);

val SUB_EQUALw = store_thm("SUB_EQUALw",
  `!a. a SUBw a = w_0`,
   RW_TAC std_ss [SUBw_def,ADD_TWO_COMP]
);

val ADD_SUBw = store_thm("ADD_SUBw",
  `!a b. a ADDw b SUBw b = a`,
  RW_TAC std_ss [ADD_SUB_ASSOC,SUB_EQUALw,ADD_0w]
);

val SUB_ADDw = REWRITE_RULE [ADD_SUB_SYM] ADD_SUBw;

val SUB_SUBw = store_thm("SUB_SUBw",
  `!a b c. a SUBw (b SUBw c) = a ADDw c SUBw b`,
  RW_TAC word_ss [SUBw_def,TWO_COMP_ADD,TWO_COMP_ELIM]
);

val ONE_COMP_TWO_COMP = store_thm("ONE_COMP_TWO_COMP",
  `!a. ONE_COMPw a = TWO_COMPw a SUBw w_1`,
  RW_TAC std_ss [TWO_COMP_ONE_COMP,ADD_SUBw]
);

val SUBw = store_thm("SUBw",
  `!m n. SUCw m SUBw n = SUCw (m SUBw n)`,
  RW_TAC std_ss [ADD1w,ADD_SUB_SYM]
);

val ADD_EQ_SUBw = store_thm("ADD_EQ_SUBw",
  `!m n p. (m ADDw n = p) = (m = p SUBw n)`,
  REPEAT STRIP_TAC THEN EQ_TAC
    THEN RW_TAC std_ss [SUB_ADDw]
    THEN REWRITE_TAC [ADD_SUBw]
);

val CANCEL_SUBw = store_thm("CANCEL_SUBw",
  `!m n p. (n SUBw p = m SUBw p) = (n = m)`,
  REPEAT STRIP_TAC THEN EQ_TAC
    THEN RW_TAC std_ss [GSYM ADD_EQ_SUBw,ADD_SUBw,SUB_ADDw]
);

val SUB_PLUSw = store_thm("SUB_PLUSw",
  `!a b c. a SUBw (b ADDw c) = a SUBw b SUBw c`,
  RW_TAC word_ss [SUBw_def,TWO_COMP_ADD]
);

(* -------------------------------------------------------- *)
 
val EQUIV_EXISTS = prove(`!y. ?x. $EQUIVw y = $EQUIVw x`, PROVE_TAC []);

val mk_word_eq_one_one = SIMP_RULE std_ss [EQUIV_EXISTS] (SPECL [`$EQUIVw x`,`$EQUIVw y`] mk_word_one_one);

val dest_word_mk_word_eq = prove(
  `!a. dest_word (mk_word ($EQUIVw a)) = $EQUIVw a`,
  STRIP_TAC THEN SIMP_TAC std_ss [EQUIV_EXISTS,GSYM (BETA_RULE word_tybij)]
);

val dest_word_mk_word_eq2 = prove(
  `!a x. (dest_word (mk_word ($EQUIVw a)) x) = (a EQUIVw x)`,
  STRIP_TAC THEN REWRITE_TAC [dest_word_mk_word_eq]
);

(* |- !a. dest_word (mk_word (EQUIVw a)) = EQUIVw a *)
val dest_word_mk_word_eq3 = save_thm("dest_word_mk_word_eq3",
  GEN_ALL (REWRITE_RULE [GSYM FUN_EQ_THM] (GEN `x` (SPEC_ALL dest_word_mk_word_eq2)))
);

val dest_word_mk_word_exists = prove(
  `?x. dest_word (mk_word ($EQUIVw a)) x`,
  RW_TAC std_ss [dest_word_mk_word_eq2,EQUIVw_def] THEN PROVE_TAC []
);

val SELECT_WORD_TAC =
    `!p:num -> bool. $@p = @x. p x` by
              (GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN PROVE_TAC [])
    THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC [th]) THEN SELECT_TAC
    THEN RW_TAC std_ss [dest_word_mk_word_exists,dest_word_mk_word_eq2];

val NUMw_EVAL = store_thm("NUMw_EVAL",
  `!n. NUMw (wn n) = MODw n`,
  RW_TAC std_ss [NUMw_def,wn_def]
    THEN SELECT_WORD_TAC
    THEN FULL_SIMP_TAC std_ss [EQUIVw_def]
);

(* -------------------------------------------------------- *)
 
val MODw_ELIM = store_thm("MODw_ELIM",
  `!n. wn (MODw n) = wn n`,
  RW_TAC std_ss [wn_def,mk_word_eq_one_one]
    THEN ONCE_REWRITE_TAC [FUN_EQ_THM]
    THEN REWRITE_TAC [EQUIVw_def,MODw_IDEM2]
);

val ADD_EVAL = store_thm("ADD_EVAL",
  `(wn a) ADDw (wn b) = wn (a + b)`,
  SIMP_TAC std_ss [wn_def,ADDw_def,mk_word_eq_one_one]
    THEN SELECT_WORD_TAC
    THEN REWRITE_TAC [GSYM EQUIVw_QT]
    THEN `a + b EQUIVw x + x'` by IMP_RES_TAC ADD_WELLDEF
    THEN ASM_SIMP_TAC std_ss [EQUIVw_SYM]
);

val MUL_EVAL = store_thm("MUL_EVAL",
  `(wn a) MULw (wn b) = wn (a * b)`,
  SIMP_TAC std_ss [wn_def,MULw_def,mk_word_eq_one_one]
    THEN SELECT_WORD_TAC
    THEN REWRITE_TAC [GSYM EQUIVw_QT]
    THEN `a * b EQUIVw x * x'` by IMP_RES_TAC MUL_WELLDEF
    THEN ASM_SIMP_TAC std_ss [EQUIVw_SYM]
);

val ONE_COMP_EVAL = store_thm("ONE_COMP_EVAL",
  `ONE_COMPw (wn a) = wn (ONE_COMP a)`,
  SIMP_TAC std_ss [wn_def,ONE_COMPw_def,mk_word_eq_one_one]
    THEN SELECT_WORD_TAC
    THEN ONCE_REWRITE_TAC [FUN_EQ_THM]
    THEN FULL_SIMP_TAC std_ss [EQUIVw_def,ONE_COMP_def]
);

val TWO_COMP_EVAL = store_thm("TWO_COMP_EVAL",
  `TWO_COMPw (wn a) = wn (TWO_COMP a)`,
  SIMP_TAC std_ss [wn_def,TWO_COMPw_def,mk_word_eq_one_one]
    THEN SELECT_WORD_TAC
    THEN ONCE_REWRITE_TAC [FUN_EQ_THM]
    THEN FULL_SIMP_TAC std_ss [EQUIVw_def,TWO_COMP_def]
);

val LSR_ONE_EVAL = store_thm("LSR_ONE_EVAL",
  `LSR_ONEw (wn a) = wn (LSR_ONE a)`,
  SIMP_TAC std_ss [wn_def,LSR_ONEw_def,LSR_ONE_def,mk_word_eq_one_one]
    THEN SELECT_WORD_TAC
    THEN REWRITE_TAC [GSYM EQUIVw_QT]
    THEN IMP_RES_TAC LSR_ONE_WELLDEF
    THEN FULL_SIMP_TAC std_ss [LSR_ONE_def,EQUIVw_SYM]
);

val ASR_ONE_EVAL = store_thm("ASR_ONE_EVAL",
  `ASR_ONEw (wn a) = wn (ASR_ONE a)`,
  SIMP_TAC std_ss [wn_def,ASR_ONEw_def,mk_word_eq_one_one]
    THEN SELECT_WORD_TAC
    THEN REWRITE_TAC [GSYM EQUIVw_QT]
    THEN IMP_RES_TAC ASR_ONE_WELLDEF
    THEN FULL_SIMP_TAC std_ss [EQUIVw_SYM]
);

val ROR_ONE_EVAL = store_thm("ROR_ONE_EVAL",
  `ROR_ONEw (wn a) = wn (ROR_ONE a)`,
  SIMP_TAC std_ss [wn_def,ROR_ONEw_def,mk_word_eq_one_one]
    THEN SELECT_WORD_TAC
    THEN REWRITE_TAC [GSYM EQUIVw_QT]
    THEN IMP_RES_TAC ROR_ONE_WELLDEF
    THEN FULL_SIMP_TAC std_ss [EQUIVw_SYM]
);

val RRX_EVAL = store_thm("RRX_EVAL",
  `RRXw c (wn a) = wn (RRXn c a)`,
  SIMP_TAC std_ss [wn_def,RRXw_def,mk_word_eq_one_one]
    THEN SELECT_WORD_TAC
    THEN REWRITE_TAC [GSYM EQUIVw_QT]
    THEN IMP_RES_TAC RRX_WELLDEF
    THEN FULL_SIMP_TAC std_ss [EQUIVw_SYM]
);

val LSB_EVAL = store_thm("LSB_EVAL",
  `LSBw (wn a) = LSB a`,
  SIMP_TAC std_ss [wn_def,LSBw_def]
    THEN SELECT_WORD_TAC
    THEN REWRITE_TAC [GSYM EQUIVw_QT]
    THEN IMP_RES_TAC LSB_WELLDEF
    THEN FULL_SIMP_TAC std_ss [EQUIVw_SYM]
);

val MSB_EVAL = store_thm("MSB_EVAL",
  `MSBw (wn a) = MSB a`,
  SIMP_TAC std_ss [wn_def,MSBw_def]
    THEN SELECT_WORD_TAC
    THEN REWRITE_TAC [GSYM EQUIVw_QT]
    THEN IMP_RES_TAC MSB_WELLDEF
    THEN FULL_SIMP_TAC std_ss [EQUIVw_SYM]
);

val OR_EVAL = store_thm("OR_EVAL",
  `(wn a) ORw (wn b) = wn (OR a b)`,
  SIMP_TAC std_ss [wn_def,ORw_def,mk_word_eq_one_one]
    THEN SELECT_WORD_TAC
    THEN REWRITE_TAC [GSYM EQUIVw_QT]
    THEN IMP_RES_TAC OR_WELLDEF
    THEN FULL_SIMP_TAC std_ss [EQUIVw_SYM]
);

val EOR_EVAL = store_thm("EOR_EVAL",
  `(wn a) EORw (wn b) = wn (EOR a b)`,
  SIMP_TAC std_ss [wn_def,EORw_def,mk_word_eq_one_one]
    THEN SELECT_WORD_TAC
    THEN REWRITE_TAC [GSYM EQUIVw_QT]
    THEN IMP_RES_TAC EOR_WELLDEF
    THEN FULL_SIMP_TAC std_ss [EQUIVw_SYM]
);

val AND_EVAL = store_thm("AND_EVAL",
  `(wn a) ANDw (wn b) = wn (AND a b)`,
  SIMP_TAC std_ss [wn_def,ANDw_def,mk_word_eq_one_one]
    THEN SELECT_WORD_TAC
    THEN REWRITE_TAC [GSYM EQUIVw_QT]
    THEN IMP_RES_TAC AND_WELLDEF
    THEN FULL_SIMP_TAC std_ss [EQUIVw_SYM]
);

val BITS_EVAL = store_thm("BITS_EVAL",
  `!h l a. BITSw h l (wn a) = BITS h l (MODw a)`,
  RW_TAC std_ss [BITSw_def,NUMw_EVAL]
);

val BIT_EVAL = store_thm("BIT_EVAL",
  `!b a. BITw b (wn a) = BIT b (MODw a)`,
  RW_TAC std_ss [BITw_def,NUMw_EVAL]
);

val SLICE_EVAL = store_thm("SLICE_EVAL",
  `!h l a. SLICEw h l (wn a) = SLICE h l (MODw a)`,
  RW_TAC std_ss [SLICEw_def,NUMw_EVAL]
);

(* -------------------------------------------------------- *)

val MOD_MOD_DIV = store_thm("MOD_MOD_DIV",
  `!a b. 0 < b ==> INw (MODw a DIV b)`,
  REPEAT STRIP_TAC
    THEN Cases_on `b = 1`
    THENL [
      ASM_SIMP_TAC std_ss [DIV1,INw_MODw],
      REWRITE_TAC [MODw_def]
        THEN Cases_on `a MOD 2 EXP WL = 0`
        THENL [
          ASM_SIMP_TAC arith_ss [ZERO_DIV,ZERO_LT_TWOEXP,INw_def],
          RULE_ASSUM_TAC (REWRITE_RULE [NOT_ZERO_LT_ZERO])
            THEN `1 < b` by DECIDE_TAC
            THEN IMP_RES_TAC DIV_LESS
            THEN ASSUME_TAC (SPEC `a` MODw_LESS)
            THEN `a MOD 2 EXP WL DIV b < 2 EXP WL` by IMP_RES_TAC LESS_TRANS
            THEN ASM_SIMP_TAC std_ss [INw_def]
        ]
    ]
);

val MOD_MOD_DIV_2EXP = store_thm("MOD_MOD_DIV_2EXP",
  `!a n. MODw (MODw a DIV 2 EXP n) DIV 2 = MODw a DIV 2 EXP SUC n`,
   REPEAT STRIP_TAC
     THEN ASSUME_TAC (SIMP_RULE arith_ss [ZERO_LT_TWOEXP] (SPECL [`a`,`2 EXP n`] MOD_MOD_DIV))
     THEN ASM_SIMP_TAC arith_ss [ZERO_LT_TWOEXP,DIV_DIV_DIV_MULT,TOw_IDEM,
                             GSYM (ONCE_REWRITE_RULE [MULT_COMM] EXP)]
);

val LSR_EVAL = store_thm("LSR_EVAL",
  `!n. LSRw n (wn a) = wn (MODw a DIV 2 EXP n)`,
  Induct_on `n`
    THENL [
       SIMP_TAC std_ss [FUNPOW,LSRw_def,EXP,DIV1,MODw_ELIM],
       FULL_SIMP_TAC std_ss [LSRw_def,FUNPOW_THM2,LSR_ONE_EVAL,LSR_ONE_def,MOD_MOD_DIV_2EXP]
    ]
);

val LESS_SUC_EXP = prove(
  `!a b. a < 2 EXP SUC b ==> a DIV 2 < 2 EXP b`,
  RW_TAC arith_ss [EXP,SYM (REDUCE_RULE (SPECL [`a DIV 2`,`2 EXP i`,`1`] LESS_MULT_MONO)),
                   DIV_MULT_THM2,SUB_RIGHT_LESS,ZERO_LT_TWOEXP]
);

val INw_RSHIFT = store_thm("INw_RSHIFT",
  `!f n a. INw (FUNPOW (\x. x DIV 2 + SET (f x) HB) n (MODw a))`,
  Induct_on `n`
    THENL [
      SIMP_TAC std_ss [FUNPOW,INw_MODw],
      SIMP_TAC std_ss [FUNPOW_THM2]
        THEN Cases_on `f (FUNPOW (\x. x DIV 2 + SET (f x) HB) n (MODw a))`
        THENL [
          FULL_SIMP_TAC std_ss [SET_def,INw_def]
            THEN ASM_SIMP_TAC std_ss [GSYM SUB_LEFT_LESS,WL_def,EXP,TIMES2,ADD_SUB]
            THEN POP_ASSUM (fn th => ASSUME_TAC (REWRITE_RULE [WL_def] (SPECL [`f`,`a`] th)))
            THEN IMP_RES_TAC LESS_SUC_EXP,
          FULL_SIMP_TAC arith_ss [SET_def,INw_def]
            THEN Cases_on `0 < FUNPOW (\x. x DIV 2 + (if f x then 2 EXP HB else 0)) n (MODw a)`
            THENL [
              IMP_RES_TAC DIV_LESS
                THEN POP_ASSUM (fn th => ASSUME_TAC (SIMP_RULE std_ss [DECIDE``1 < 2``] (SPEC `2` th)))
                THEN PAT_ASSUM `!f a.  FUNPOW (\x. x DIV 2 + (if f x then 2 EXP HB else 0)) n
                                (MODw a) < 2 EXP WL` (fn th => ASSUME_TAC (SPECL [`f`,`a`] th))
                THEN IMP_RES_TAC LESS_TRANS,
              RULE_ASSUM_TAC (SIMP_RULE std_ss [GSYM NOT_ZERO_LT_ZERO])
                THEN ASM_SIMP_TAC arithr_ss [ZERO_LT_TWOEXP]
            ]
        ]
    ]
);

val INw_ASR = SPEC `MSB` INw_RSHIFT;
val INw_ROR = SPEC `LSB` INw_RSHIFT;

val ASR_EVAL = store_thm("ASR_EVAL",
  `!n a. ASRw n (wn a) = wn (FUNPOW (\x. x DIV 2 + SET (MSB x) HB) n (MODw a))`,
  Induct_on `n`
    THEN STRIP_TAC
    THENL [
       SIMP_TAC std_ss [FUNPOW,ASRw_def,ASR_ONEw_def,ASR_ONE_def,LSR_ONE_def,MODw_ELIM],
       RULE_ASSUM_TAC (REWRITE_RULE [ASRw_def])
         THEN ASSUME_TAC (SPECL [`n`,`a`] INw_ASR)
         THEN ASM_SIMP_TAC std_ss [ASRw_def,FUNPOW_THM2,ASR_ONE_EVAL,
                                   GSYM ADD_EVAL,ASR_ONE_def,LSR_ONE_def,MODw_ELIM,TOw_IDEM]
    ]
);

val ROR_EVAL = store_thm("ROR_EVAL",
  `!n a. RORw n (wn a) = wn (FUNPOW (\x. x DIV 2 + SET (LSB x) HB) n (MODw a))`,
  Induct_on `n`
    THEN STRIP_TAC
    THENL [
       SIMP_TAC std_ss [FUNPOW,RORw_def,ROR_ONEw_def,ROR_ONE_def,LSR_ONE_def,MODw_ELIM],
       RULE_ASSUM_TAC (REWRITE_RULE [RORw_def])
         THEN ASSUME_TAC (SPECL [`n`,`a`] INw_ROR)
         THEN ASM_SIMP_TAC std_ss [RORw_def,FUNPOW_THM2,ROR_ONE_EVAL,
                                   GSYM ADD_EVAL,ROR_ONE_def,LSR_ONE_def,MODw_ELIM,TOw_IDEM]
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
val MSB_EVAL2 = save_thm("MSB_EVAL2",GEN_ALL (REWRITE_RULE [MSB_def,HB_def] MSB_EVAL));

val OR_EVAL2 = save_thm("OR_EVAL2",GEN_ALL (SIMP_RULE std_ss [OR_def,THE_WL] OR_EVAL));
val AND_EVAL2 = save_thm("AND_EVAL2",GEN_ALL (SIMP_RULE std_ss [AND_def,THE_WL] AND_EVAL));
val EOR_EVAL2 = save_thm("EOR_EVAL2",GEN_ALL (SIMP_RULE std_ss [EOR_def,THE_WL] EOR_EVAL));

(* -------------------------------------------------------- *)

val BITWISE_EVAL2 = store_thm("BITWISE_EVAL2",
  `!n op x y. BITWISE n op x y =
                 if n = 0 then 0
                 else let r = BITWISE (n - 1) op (x DIV 2) (y DIV 2) in
                   if op (LSB x) (LSB y) then r + r + 1 else r + r`,
  REPEAT STRIP_TAC
    THEN Cases_on `n = 0`
    THEN ASM_SIMP_TAC std_ss [BITWISE_def]
    THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_ZERO_LT_ZERO])
    THEN IMP_RES_TAC LESS_ADD_1
    THEN `n = SUC p` by RW_TAC arith_ss []
    THEN ASM_SIMP_TAC arith_ss [BITWISE_def]
);

(* -------------------------------------------------------- *)

val BITSwLT_THM = store_thm("BITSwLT_THM",
  `!h l n. BITSw h l n < 2 EXP (SUC h-l)`,
  RW_TAC std_ss [BITSLT_THM,BITSw_def]
);

val BITSw_COMP_THM = store_thm("BITSw_COMP_THM",
  `!h1 l1 h2 l2 n. h2 + l1 <= h1 ==> (BITS h2 l2 (BITSw h1 l1 n) = BITSw (h2+l1) (l2+l1) n)`,
  RW_TAC std_ss [BITSw_def,BITS_COMP_THM]
);
 
val BITSw_DIV_THM = store_thm("BITSw_DIV_THM",
  `!h l n x. (BITSw h l x) DIV 2 EXP n = BITSw h (l + n) x`,
  RW_TAC std_ss [BITSw_def,BITS_DIV_THM]
);

val BITw_THM = store_thm("BITw_THM",
  `!b n. BITw b n = (BITSw b b n = 1)`,
  RW_TAC std_ss [BITSw_def,BITw_def,BIT_def]
);
 
val SLICEw_THM = store_thm("SLICEw_THM",
  `!n h l. SLICEw h l n = BITSw h l n * 2 EXP l`,
  RW_TAC std_ss [SLICEw_def,BITSw_def,SLICE_THM]
);

val BITS_SLICEw_THM = store_thm("BITS_SLICEw_THM",
  `!h l n. BITS h l (SLICEw h l n) = BITSw h l n`,
  RW_TAC std_ss [SLICEw_def,BITSw_def,BITS_SLICE_THM]
);

val SLICEw_ZERO_THM = store_thm("SLICEw_ZERO_THM",
  `!n h. SLICEw h 0 n = BITSw h 0 n`,
  RW_TAC arithr_ss [SLICEw_THM]
);
 
val SLICEw_COMP_THM = store_thm("SLICEw_COMP_THM",
  `!h m l a. (SUC m) <= h /\ l <= m ==> (SLICEw h (SUC m) a + SLICEw m l a = SLICEw h l a)`,
  RW_TAC std_ss [SLICEw_def,SLICE_COMP_THM]
);

(* -------------------------------------------------------- *)

val _ = export_theory();
 
(* -------------------------------------------------------- *)
