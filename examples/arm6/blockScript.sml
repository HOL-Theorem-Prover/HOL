(* app load ["pred_setSimps","metisLib","bitsTheory","sum_numTheory","my_listTheory",
             "armTheory","coreTheory","lemmasTheory","compLib","interruptsTheory"]; *)
open HolKernel boolLib bossLib Q arithmeticTheory whileTheory rich_listTheory
     my_listTheory bitsTheory word32Theory sum_numTheory armTheory coreTheory
     lemmasTheory compLib interruptsTheory;

(* -------------------------------------------------------- *)

val _ = new_theory "block";

val _ = numLib.prefer_num();

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

(* -------------------------------------------------------- *)

val GEN_REG_LIST_def = Define`
  GEN_REG_LIST wl n = (MAP SND o FILTER FST) (GENLIST (\b. (BIT b n,b)) wl)`;

val GEN_RP_def = Define`
  GEN_RP wl ireg mask = LEASTBIT (BITWISE wl $/\ ireg mask)`;

val MASK_BIT_def = Define`
  MASK_BIT wl ireg mask = CLEARBIT wl (GEN_RP wl ireg mask) mask`;

val MASKN_def = Define`
  MASKN wl n ireg = FUNPOW (MASK_BIT wl ireg) n (ONECOMP wl 0)`;

val REG_WRITE_RP_def = Define`
  REG_WRITE_RP n reg mode ireg data =
    REG_WRITE reg mode (RP ldm ireg (MASKN 16 n ireg)) data`;

val REG_WRITEN_def = Define`
  (REG_WRITEN 0 reg mode ireg i = reg) /\
  (REG_WRITEN (SUC n) reg mode ireg i =
     REG_WRITE_RP n (REG_WRITEN n reg mode ireg i) mode ireg (PROJ_DATA (i n)))`;

(* -------------------------------------------------------- *)

val LEAST_THM = io_onestepTheory.LEAST_THM;

val lem = prove(
  `!a x. x < 16 ==> ((\b. (BIT b a,b)) x = (\b. (BIT b (BITS 15 0 a),b)) x)`,
  RW_TAC arith_ss [MIN_DEF,BITS_COMP_THM2,BIT_def]
);

val SPEC_GENLIST_FUN_EQ = (GEN_ALL o REWRITE_RULE [lem] o
  ISPECL [`\b. (BIT b a,b)`,`\b. (BIT b (BITS 15 0 a),b)`] o SPEC `16`) GENLIST_FUN_EQ;

val REGISTER_LIST_150 = store_thm("REGISTER_LIST_150",
  `!a. REGISTER_LIST (BITS 15 0 a) = REGISTER_LIST a`,
  REWRITE_TAC [REGISTER_LIST_def,GSYM SPEC_GENLIST_FUN_EQ]
);

val REGISTER_LIST_WORD150 =
  (GEN_ALL o REWRITE_RULE [GSYM WORD_BITS_def] o SPEC `w2n a`) REGISTER_LIST_150;

(* -------------------------------------------------------- *)

val BITV_THM2 = prove(
  `!n. BITV n = \b. SBIT (BIT b n) 0`,
  REWRITE_TAC [FUN_EQ_THM] THEN SIMP_TAC std_ss [BITV_THM]
);

(* -------------------------------------------------------- *)

val BITWISE_ONE_COMP_LEM2 = prove(
  `!wl a b. BITWISE wl (\x y. ~x) a b = ONECOMP wl a`,
  Cases THEN1 SIMP_TAC arith_ss [BITWISE_def,ONECOMP_def]
    THEN REWRITE_TAC [BITWISE_ONE_COMP_LEM,ONECOMP_def,BITS_ZERO3]
);

val ONE_COMP_THM2 = prove(
  `!a x. x < wl ==> (BIT x (ONECOMP wl a) = ~BIT x a)`,
  REWRITE_TAC [GSYM BITWISE_ONE_COMP_LEM2] THEN RW_TAC bool_ss [BITWISE_THM]
);

val ZERO_IS_FALSE = prove(`!x. ~BIT x 0`,RW_TAC arith_ss [BIT_def,BITS_ZERO2]);

val ONE_COMP_TRUE = REWRITE_RULE [ZERO_IS_FALSE] (SPEC `0` ONE_COMP_THM2);

(* -------------------------------------------------------- *)

val NOT_ADD = prove(
  `!a b. NOT a + b = b - (a + 1w)`,
  REWRITE_TAC [WORD_NOT,GSYM WORD_ADD_SUB_SYM,WORD_SUB_PLUS,WORD_LCANCEL_SUB,WORD_SUB]
);

val NOT_ADD_1 = prove(
  `!a b. NOT a + b + 1w = b - a`,
  REWRITE_TAC [WORD_NOT,GSYM WORD_ADD_SUB_SYM,WORD_ADD_SUB,WORD_SUB]
);

val MULT_ADD_FOUR = prove(
  `!a x. a + w32 x * w32 4 + w32 4 = a + w32 (SUC x) * w32 4`,
  REWRITE_TAC [GSYM (List.nth ((CONJUNCTS o SPEC_ALL) WORD_MULT_CLAUSES,4)),
               GSYM WORD_ADD_ASSOC,ADD1,WORD_ADD1,ADD_EVAL]
);

val MULT_ADD_FOUR2 = prove(
  `!a b c:word32. a + b + c = a + c + b`,
  REWRITE_TAC [GSYM WORD_ADD_ASSOC,WORD_EQ_ADD_LCANCEL]
    THEN PROVE_TAC [WORD_ADD_COMM]
);

val MULT_ADD_FOUR2 = ONCE_REWRITE_RULE [MULT_ADD_FOUR2] MULT_ADD_FOUR;

(* -------------------------------------------------------- *)

val CLEARBIT_THM = prove(
  `!wl b a. ~BIT b (CLEARBIT wl b a)`,
  Cases THEN1 SIMP_TAC arith_ss [CLEARBIT_def,BITWISE_def,BIT_def,BITS_ZERO2]
    THEN REWRITE_TAC [GSYM BITWISE_ONE_COMP_LEM,CLEARBIT_def,ONECOMP_def,GSYM BITS_ZERO3]
    THEN NTAC 2 STRIP_TAC THEN Cases_on `b < SUC n`
    THEN1 ASM_SIMP_TAC bool_ss [BITWISE_THM,BIT_B]
    THEN FULL_SIMP_TAC bool_ss [NOT_LESS,BIT_def,BITS_THM,SUC_SUB]
    THEN ASSUME_TAC (SPECL [`SUC n`,`$/\`,`a`,`BITWISE (SUC n) (\x y. ~x) (2 ** b) b`] BITWISE_LT_2EXP)
    THEN IMP_RES_TAC TWOEXP_MONO2
    THEN IMP_RES_TAC LESS_LESS_EQ_TRANS
    THEN ASM_SIMP_TAC arith_ss [LESS_DIV_EQ_ZERO]
);

val CLEARBIT_THM2 = prove(
  `!wl a b c. ~(a = b) /\ (a < wl) ==>
      (BIT a (CLEARBIT wl b c) = BIT a c)`,
  Cases THEN1 SIMP_TAC arith_ss []
    THEN REWRITE_TAC [GSYM BITWISE_ONE_COMP_LEM,CLEARBIT_def,ONECOMP_def,GSYM BITS_ZERO3]
    THEN NTAC 4 STRIP_TAC THEN Cases_on `b < SUC n`
    THEN ASM_SIMP_TAC bool_ss [BITWISE_THM,BIT_B_NEQ]
);

(* -------------------------------------------------------- *)

val GEN_REG_LIST_ZERO = prove(
  `!n. GEN_REG_LIST 0 n = []`,
  SIMP_TAC list_ss [GENLIST,FILTER,MAP,GEN_REG_LIST_def]
);

val GEN_REG_LIST_THM = prove(
  `!wl n. GEN_REG_LIST (SUC wl) n =
         if BIT wl n then SNOC wl (GEN_REG_LIST wl n)
                     else GEN_REG_LIST wl n`,
  RW_TAC std_ss [GEN_REG_LIST_def,GENLIST,FILTER_SNOC,MAP_SNOC]
);

val REGISTER_LIST_LEM = store_thm("REGISTER_LIST_LEM",
  `!wl n. LENGTH (GEN_REG_LIST wl n) = SUM wl (BITV n)`,
  Induct THEN1 REWRITE_TAC [GEN_REG_LIST_ZERO,LENGTH,SUM_def]
    THEN RW_TAC arith_ss [SUM_def,GEN_REG_LIST_THM,BITV_THM2,SBIT_def,LENGTH_SNOC,ADD1]
);

(* -------------------------------------------------------- *)

val MASKN_ZERO = store_thm("MASKN_ZERO",
  `!wl ireg. MASKN wl 0 ireg = ONECOMP wl 0`,
  REWRITE_TAC [MASKN_def,FUNPOW]
);

val MASKN_SUC = prove(
  `!wl n ireg. MASKN wl (SUC n) ireg = MASK_BIT wl ireg (MASKN wl n ireg)`,
  REWRITE_TAC [MASKN_def,FUNPOW_SUC]
);

val MASKN_THM = prove(
  `!p wl ireg.
     (!x. p <= x /\ x < wl ==>
       BIT x (MASKN wl (SUM p (BITV ireg)) ireg)) /\
     (!x. x < p /\ p <= wl ==>
       ~BIT x (BITWISE wl (/\) ireg (MASKN wl (SUM p (BITV ireg)) ireg)))`,
  REWRITE_TAC [BITV_THM2]
    THEN Induct THEN1 SIMP_TAC bool_ss [prim_recTheory.NOT_LESS_0,SUM_def,MASKN_def,FUNPOW,ONE_COMP_TRUE]
    THEN NTAC 2 STRIP_TAC
    THEN POP_ASSUM (SPECL_THEN [`wl`,`ireg`] (STRIP_ASSUME_TAC o SIMP_RULE arith_ss [SBIT_def]))
    THEN RW_TAC arith_ss [SUM_def,SBIT_def,GSYM ADD1]
    THEN REWRITE_TAC [MASKN_SUC,MASK_BIT_def,GEN_RP_def,LEASTBIT_def]
    THENL [
      `BIT p (BITWISE wl $/\ ireg (MASKN wl (SUM p (\b. (if BIT b ireg then 1 else 0))) ireg))`
          by ASM_SIMP_TAC arith_ss [BITWISE_THM]
        THEN IMP_RES_TAC ((SPEC `p` o SIMP_RULE bool_ss [] o INST [`P` |-> `\b. BIT b
               (BITWISE wl $/\ ireg (MASKN wl (SUM p (\b. (if BIT b ireg then 1 else 0))) ireg))`]) LEAST_THM)
        THEN ASM_SIMP_TAC arith_ss [CLEARBIT_THM2],
      `BIT p (BITWISE wl $/\ ireg (MASKN wl (SUM p (\b. (if BIT b ireg then 1 else 0))) ireg))`
          by ASM_SIMP_TAC arith_ss [BITWISE_THM]
        THEN IMP_RES_TAC ((SPEC `p` o SIMP_RULE bool_ss [] o INST [`P` |-> `\b. BIT b
               (BITWISE wl $/\ ireg (MASKN wl (SUM p (\b. (if BIT b ireg then 1 else 0))) ireg))`]) LEAST_THM)
        THEN Cases_on `x < p` THEN1 FULL_SIMP_TAC arith_ss [CLEARBIT_THM2,BITWISE_THM]
        THEN `x = p` by DECIDE_TAC THEN FULL_SIMP_TAC arith_ss [CLEARBIT_THM,BITWISE_THM],
      Cases_on `x < p` THEN1 ASM_SIMP_TAC arith_ss []
        THEN `x = p` by DECIDE_TAC THEN ASM_SIMP_TAC arith_ss [BITWISE_THM]
    ]
);

(* -------------------------------------------------------- *)

val SUM_BITS = prove(
  `!p n.
      SUM (SUC p) (BITV n) =
        if BIT p n then
          SUC (SUM p (BITV n))
        else
          SUM p (BITV n)`,
  RW_TAC arith_ss [SUM_def,BITV_THM2,SBIT_def]
);

val SUM_BITS2 = prove(
  `!p n. BIT p n ==>
     (SUM (SUC p) (BITV n) = SUC (SUM p (BITV n)))`,
  RW_TAC bool_ss [SUM_BITS]
);

val SUM_BITS3 = prove(
  `!p n. BIT p n ==>
      (!q. q < p ==>
         ~(SUM (SUC q) (BITV n) = SUM (SUC p) (BITV n)))`,
  REPEAT STRIP_TAC
    THEN `~(BITV n p = 0)` by ASM_SIMP_TAC arith_ss [GSYM BIT_def,NOT_BITS,BITV_def]
    THEN IMP_RES_TAC ((GEN_ALL o REWRITE_RULE [GSYM LESS_EQ] o SPEC `SUC m`) SUM_MONO)
    THEN DECIDE_TAC
);

val EL_GEN_REG_LIST = prove(
  `!x wl n. x < LENGTH (GEN_REG_LIST wl n) ==>
               (EL x (GEN_REG_LIST wl n) =
                $LEAST (\p. SUM (SUC p) (BITV n) = SUC x))`,
  Induct_on `wl` THEN1 REWRITE_TAC [prim_recTheory.NOT_LESS_0,GEN_REG_LIST_ZERO,LENGTH]
    THEN RW_TAC arith_ss [GEN_REG_LIST_THM,LENGTH_SNOC]
    THEN Cases_on `x < LENGTH (GEN_REG_LIST wl n)`
    THEN1 ASM_SIMP_TAC bool_ss [EL_SNOC]
    THEN `x = LENGTH (GEN_REG_LIST wl n)` by DECIDE_TAC
    THEN ASM_SIMP_TAC bool_ss [EL_LENGTH_SNOC]
    THEN ASM_SIMP_TAC bool_ss [REGISTER_LIST_LEM,GSYM SUM_BITS2]
    THEN IMP_RES_TAC SUM_BITS3
    THEN IMP_RES_TAC ((SIMP_RULE bool_ss [] o SPEC `wl` o INST [`P` |->
              `\x. SUM (SUC x) (BITV n) = SUM (SUC wl) (BITV n)`]) LEAST_THM)
    THEN ASM_REWRITE_TAC []
);

val EXISTS_SUM_BITS = prove(
  `!x wl n. x < LENGTH (GEN_REG_LIST wl n) ==>
     ?p. p < wl /\ (x = SUM p (BITV n))`,
  Induct_on `wl` THEN1 REWRITE_TAC [prim_recTheory.NOT_LESS_0,GEN_REG_LIST_ZERO,LENGTH]
    THEN RW_TAC arith_ss [GEN_REG_LIST_THM,LENGTH_SNOC]
    THENL [
       Cases_on `x < LENGTH (GEN_REG_LIST wl n)`
         THENL [
           PAT_ASSUM `!x n. P` IMP_RES_TAC
             THEN `p < SUC wl` by DECIDE_TAC THEN PROVE_TAC [],
           `x = LENGTH (GEN_REG_LIST wl n)` by DECIDE_TAC
             THEN FULL_SIMP_TAC bool_ss [REGISTER_LIST_LEM]
             THEN EXISTS_TAC `wl` THEN SIMP_TAC arith_ss []
         ],
       PAT_ASSUM `!x n. P` IMP_RES_TAC
         THEN `p < SUC wl` by DECIDE_TAC THEN PROVE_TAC []
    ]
);

val SUM_LT = prove(
  `!p m n. SUM p (BITV n) < SUM m (BITV n) ==>
             ?y. p <= y /\ y < m /\
                     BIT y ((BITWISE m $/\ n (MASKN m (SUM p (BITV n)) n))) /\
               (!q. q < y ==> ~BIT q
                     (BITWISE m $/\ n (MASKN m (SUM p (BITV n)) n)))`,
  REPEAT STRIP_TAC
    THEN POP_ASSUM (ASSUME_TAC o (MATCH_MP ((GEN_ALL o snd o EQ_IMP_RULE o SPEC_ALL) SUM_LESS)))
    THEN RULE_ASSUM_TAC (SIMP_RULE arith_ss [BITV_THM,SBIT_def,
           metisLib.METIS_PROVE [DECIDE ``~(1 = 0)``] ``!a. ((if a then 1 else 0) = 0) = ~a``])
    THEN RULE_ASSUM_TAC (REWRITE_RULE [(SIMP_RULE std_ss [] o
            SPEC `\y. p <= y /\ y < m /\ BIT y n`) LEAST_EXISTS])
    THEN ABBREV_TAC `z = LEAST y. p <= y /\ y < m /\ BIT y n`
    THEN POP_ASSUM (K ALL_TAC)
    THEN EXISTS_TAC `z`
    THEN RW_TAC arith_ss [] THEN1 ASM_SIMP_TAC bool_ss [MASKN_THM,BITWISE_THM]
    THEN PAT_ASSUM `!n. P` (IMP_RES_TAC o SPEC `q`)
    THEN FULL_SIMP_TAC arith_ss []
    THEN1 (`q < p /\ p <= m` by DECIDE_TAC THEN ASM_SIMP_TAC bool_ss [MASKN_THM])
    THEN ASM_SIMP_TAC arith_ss [BITWISE_THM]
);

val lem3a = prove(
  `!y p m n. p <= y /\ y < m /\
     BIT y (BITWISE m $/\ n
               (MASKN m (SUM p (BITV n)) n)) /\
     (!q. q < y ==>
            ~BIT q
               (BITWISE m $/\ n
                  (MASKN m (SUM p (BITV n)) n))) ==>
     (p <= y /\ BIT y n /\
       (!q. q < y ==> ~(p <= q /\ BIT q n)))`,
  RW_TAC bool_ss []
    THEN1 PAT_ASSUM `y < m` (fn th => FULL_SIMP_TAC bool_ss [BITWISE_THM,th])
    THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
    THEN PAT_ASSUM `!q. P` (SPEC_THEN `q` IMP_RES_TAC)
    THEN `q < m` by DECIDE_TAC
    THEN POP_ASSUM (fn th => FULL_SIMP_TAC arith_ss [th,BITWISE_THM] THEN ASSUME_TAC th)
    THEN1 PROVE_TAC []
    THEN IMP_RES_TAC ((CONJUNCT1 o SPECL [`p`,`m`,`n`]) MASKN_THM)
    THEN NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN POP_ASSUM (SPEC_THEN `n` ASSUME_TAC)
    THEN PROVE_TAC []
);

val SPEC_SUM_EQUAL2 = (GEN_ALL o SIMP_RULE std_ss [BITV_def,GSYM NOT_BIT] o
               SPECL [`p`,`y`,`BITV n`]) SUM_EQUAL;
val SPEC_SUM_EQUAL3 = PROVE [SUM_EQUAL]
                      ``!m n f. m <= n /\ (!q. m <= q /\ q < n ==> (f q = 0)) ==>
                        (SUM m f = SUM n f)``;
val SPEC_SUM_EQUAL4 = (GEN_ALL o SIMP_RULE std_ss [BITV_def,GSYM NOT_BIT] o
               SPECL [`p`,`y`,`BITV n`]) SPEC_SUM_EQUAL3;

val lem3b = prove(
  `!y p m n.
   (p <= y /\ BIT y n /\
       (!q. q < y ==> ~(p <= q /\ BIT q n))) ==>
   ((SUM (SUC y) (BITV n) = SUC (SUM p (BITV n))) /\
    (!q. q < y ==> ~(SUM (SUC q) (BITV n) = SUC (SUM p (BITV n)))))`,
  RW_TAC arith_ss [SUM_def,BITV_THM,SBIT_def,GSYM ADD1]
    THEN RULE_ASSUM_TAC (REWRITE_RULE [DECIDE (Term `!a b c. (a ==> ~b \/ c) = (b /\ a ==> c)`)])
    THENL [
      Cases_on `p = y` THEN1 PROVE_TAC []
        THEN `p < y` by DECIDE_TAC
        THEN IMP_RES_TAC SPEC_SUM_EQUAL2,
      RW_TAC arith_ss [GSYM ADD1,SPEC_SUM_EQUAL2]
        THENL [
          Cases_on `~(q <= p)` THEN1 PROVE_TAC []
            THEN FULL_SIMP_TAC arith_ss []
            THEN Cases_on `q < p` THEN1 PROVE_TAC [LESS_EQ_REFL]
            THEN `p <= q` by DECIDE_TAC
            THEN PROVE_TAC [],
          Cases_on `~(p < q)` THEN1 PROVE_TAC []
            THEN FULL_SIMP_TAC arith_ss []
            THEN `p <= q` by DECIDE_TAC
            THEN PROVE_TAC [],
          IMP_RES_TAC SPEC_SUM_EQUAL4
            THEN ASM_SIMP_TAC arith_ss []
            THEN `SUC (SUM y (BITV n)) = SUM (SUC y) (BITV n)`
              by FULL_SIMP_TAC arith_ss [BITV_def,SBIT_def,BIT_def,SUM_def]
            THEN POP_ASSUM SUBST1_TAC
            THEN `q <= y` by DECIDE_TAC
            THEN IMP_RES_TAC ((GEN_ALL o SIMP_RULE arith_ss [BITV_def,GSYM NOT_BIT] o
                   SPECL [`q`,`y`,`BITV n`]) SUM_MONO)
            THEN DECIDE_TAC
        ]
    ]
);

val lem3 = GEN_ALL (IMP_TRANS (SPEC_ALL lem3a) (SPEC_ALL lem3b));

val REGISTER_LIST_LEM2 = store_thm("REGISTER_LIST_LEM2",
  `!wl n x. x < LENGTH (GEN_REG_LIST wl n) ==> (EL x (GEN_REG_LIST wl n) = GEN_RP wl n (MASKN wl x n))`,
  RW_TAC bool_ss [EL_GEN_REG_LIST]
    THEN IMP_RES_TAC EXISTS_SUM_BITS
    THEN FULL_SIMP_TAC bool_ss [GEN_RP_def,LEASTBIT_def,BITWISE_THM,REGISTER_LIST_LEM]
    THEN IMP_RES_TAC SUM_LT
    THEN IMP_RES_TAC ((SIMP_RULE bool_ss [] o SPEC `y` o INST [`P` |-> `\b. BIT b
            (BITWISE wl $/\ n (MASKN wl (SUM p (BITV n)) n))`]) LEAST_THM)
    THEN IMP_RES_TAC lem3 THEN NTAC 8 (POP_ASSUM (K ALL_TAC))
    THEN IMP_RES_TAC ((SIMP_RULE bool_ss [] o SPEC `y` o INST [`P` |-> `\p'.
            SUM (SUC p') (BITV n) = SUC (SUM p (BITV n))`]) LEAST_THM)
    THEN ASM_REWRITE_TAC []
);

(* -------------------------------------------------------- *)

val ADDRESS_LIST_LEM = prove(
  `!base n x y. x < y ==> (EL x (ADDRESS_LIST base y) = base + w32 x * w32 4)`,
  RW_TAC bool_ss [ADDRESS_LIST_def,EL_GENLIST,MUL_EVAL] THEN PROVE_TAC [MULT_COMM]
);

val MUST_BE_EQUAL = DECIDE (Term `!x y. x < SUC y /\ ~(x < y) ==> (x = y)`);

val EL_GEN_REG_LIST_LT_WL = prove(
  `!wl x n. x < LENGTH (GEN_REG_LIST wl n) ==> (EL x (GEN_REG_LIST wl n) < wl)`,
  Induct THEN1 SIMP_TAC list_ss [GEN_REG_LIST_ZERO]
    THEN RW_TAC std_ss [GEN_REG_LIST_def,GENLIST,FILTER_SNOC,MAP_SNOC,LENGTH_SNOC]
    THEN FULL_SIMP_TAC arith_ss [(GSYM o SIMP_RULE std_ss []) GEN_REG_LIST_def,
                                 EL_SNOC,(GSYM o CONJUNCT1) EL,prim_recTheory.LESS_SUC]
    THEN Cases_on `x < LENGTH (GEN_REG_LIST wl n)`
    THEN1 ASM_SIMP_TAC arith_ss [EL_SNOC,prim_recTheory.LESS_SUC]
    THEN IMP_RES_TAC MUST_BE_EQUAL
    THEN ASM_SIMP_TAC arith_ss [EL_LENGTH_SNOC]
);

val GEN_RP_LT_WL = prove(
  `!wl x n. x < LENGTH (GEN_REG_LIST wl n) ==> (GEN_RP wl n (MASKN wl x n) < wl)`,
  SIMP_TAC bool_ss [GSYM REGISTER_LIST_LEM2,EL_GEN_REG_LIST_LT_WL]
);

(* -------------------------------------------------------- *)

val RP_GEN_RP = prove(
  `(RP ldm = GEN_RP 16) /\ (RP stm = GEN_RP 16)`,
  REWRITE_TAC [FUN_EQ_THM,GEN_RP_def,RP_def]
);

val REGISTER_LIST_GEN_REG_LIST =
  (REWRITE_RULE [GSYM FUN_EQ_THM,GSYM REGISTER_LIST_def] o SPEC `16`) GEN_REG_LIST_def;

val EL_GEN_REG_LIST_EQUAL = prove(
  `!wl x y n. x < LENGTH (GEN_REG_LIST wl n) /\ y < LENGTH (GEN_REG_LIST wl n) ==>
              ((EL x (GEN_REG_LIST wl n) = EL y (GEN_REG_LIST wl n)) = (x = y))`,
  Induct THEN1 SIMP_TAC list_ss [GEN_REG_LIST_ZERO]
    THEN RW_TAC std_ss [GEN_REG_LIST_def,GENLIST,FILTER_SNOC,MAP_SNOC,LENGTH_SNOC]
    THEN FULL_SIMP_TAC arith_ss [(GSYM o SIMP_RULE std_ss []) GEN_REG_LIST_def,EL_SNOC,(GSYM o CONJUNCT1) EL]
    THEN Cases_on `x < LENGTH (GEN_REG_LIST wl n)`
    THEN Cases_on `y < LENGTH (GEN_REG_LIST wl n)`
    THEN ASM_SIMP_TAC arith_ss [EL_SNOC]
    THEN IMP_RES_TAC EL_GEN_REG_LIST_LT_WL
    THEN IMP_RES_TAC MUST_BE_EQUAL
    THEN ASM_SIMP_TAC arith_ss [EL_LENGTH_SNOC]
);

val GEN_RP_NOT_EQUAL_ZERO = prove(
  `!wl x n. 0 < x /\ x < LENGTH (GEN_REG_LIST wl n) ==>
     ~(GEN_RP wl n (MASKN wl x n) = GEN_RP wl n (MASKN wl 0 n))`,
  SIMP_TAC arith_ss [GSYM REGISTER_LIST_LEM2,EL_GEN_REG_LIST_EQUAL]
);

val RP_NOT_EQUAL_ZERO = save_thm("RP_NOT_EQUAL_ZERO",
  (REWRITE_RULE [(SYM o CONJUNCT2) RP_GEN_RP,MASKN_ZERO,REGISTER_LIST_GEN_REG_LIST] o
   SPEC `16`) GEN_RP_NOT_EQUAL_ZERO
);

(* -------------------------------------------------------- *)

val SPEC_REGISTER_LIST_LEM =
  (GSYM o REWRITE_RULE [REGISTER_LIST_GEN_REG_LIST] o SPEC `16`) REGISTER_LIST_LEM2;

val RP_LT_16 = store_thm("RP_LT_16",
  `!x ic n. ((ic = ldm) \/ (ic = stm)) /\ x < LENGTH (REGISTER_LIST n) ==>
             RP ic n (MASKN 16 x n) < 16`,
  REWRITE_TAC [SYM REGISTER_LIST_GEN_REG_LIST]
    THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [RP_GEN_RP]
    THEN ASM_SIMP_TAC bool_ss [GEN_RP_LT_WL]
);

val RP_LT_16_0 = save_thm("RP_LT_16_0",(REWRITE_RULE [MASKN_ZERO] o SPEC `0`) RP_LT_16);

val LENGTH_TL_GENLIST = prove(
  `!n f. LENGTH (TL (GENLIST f (n + 1))) = n`,
  metisLib.METIS_TAC [LENGTH_GENLIST,LENGTH_TL,DECIDE ``!n. 0 < n + 1 /\ (n + 1 - 1 = n)``]
);

val SPEC_FOLDL_SNOC = (GEN_ALL o GSYM o SIMP_RULE std_ss [] o
     SPECL [`(\reg' (rp,rd). REG_WRITE reg' mode rp rd)`,`reg`,`(r,a)`] o
     INST_TYPE [`:'a` |-> `:num # 'a`,`:'b` |-> `:register -> 'a`]) FOLDL_SNOC;

val PROJ_DATA_EL = store_thm("PROJ_DATA_EL",
  `!x n i. SUC x <= n ==>
     (PROJ_DATA (ADVANCE 1 i x) =
        EL x (TL (GENLIST (\s. PROJ_DATA (i s)) (n + 1))))`,
  RW_TAC arith_ss [GSYM EL,EL_GENLIST,io_onestepTheory.ADVANCE_def,ADD1]
);

val REGISTER_LIST_LDM_THM = store_thm("REGISTER_LIST_LDM_THM",
  `!n x ireg reg mode i.
     x <= LENGTH (REGISTER_LIST ireg) /\ LENGTH (REGISTER_LIST ireg) <= n ==>
     (LDM_LIST reg mode (FIRSTN x (FST (ADDR_MODE4 P U base ireg)))
               (FIRSTN x (TL (GENLIST (\s. PROJ_DATA (i s)) (n + 1)))) =
      REG_WRITEN x reg mode ireg (ADVANCE 1 i))`,
  Induct_on `x` THEN REPEAT STRIP_TAC
    THEN1 SIMP_TAC list_ss [FIRSTN,LDM_LIST_def,REG_WRITEN_def]
    THEN `x <= LENGTH (REGISTER_LIST ireg)` by DECIDE_TAC
    THEN PAT_ASSUM `!n ireg reg mode i. P` (IMP_RES_TAC o GSYM)
    THEN ASM_SIMP_TAC arith_ss [REG_WRITEN_def,ADDR_MODE4_def,REG_WRITE_RP_def,
                                RP_GEN_RP,SPEC_REGISTER_LIST_LEM]
    THEN `SUC x <= n` by DECIDE_TAC
    THEN IMP_RES_TAC PROJ_DATA_EL THEN POP_ASSUM (K ALL_TAC)
    THEN POP_ASSUM (ISPEC_THEN `i` SUBST1_TAC)
    THEN `LENGTH (REGISTER_LIST ireg) <= LENGTH (TL (GENLIST (\s. PROJ_DATA (i s)) (n + 1)))`
      by ASM_SIMP_TAC arith_ss [LENGTH_TL_GENLIST]
    THEN `EL x (TL (GENLIST (\s. PROJ_DATA (i s)) (n + 1))) =
          EL x (FIRSTN (LENGTH (REGISTER_LIST ireg))
                  (TL (GENLIST (\s. PROJ_DATA (i s)) (n + 1))))` by ASM_SIMP_TAC arith_ss [GSYM EL_FIRSTN]
    THEN ASM_SIMP_TAC list_ss [LENGTH_TL_GENLIST,PROJ_DATA_EL,GSYM listTheory.EL_ZIP,SPEC_FOLDL_SNOC,
           LENGTH_FIRSTN,SNOC_EL_FIRSTN,LENGTH_ZIP,LDM_LIST_def,ZIP_FIRSTN_LEQ]
);

val FST_ADDR_MODE4 = save_thm("FST_ADDR_MODE4",
  (GEN_ALL o SIMP_CONV std_ss [ADDR_MODE4_def]) ``FST (ADDR_MODE4 P U base n)``);

val SND_ADDR_MODE4 = save_thm("SND_ADDR_MODE4",
  SIMP_CONV std_ss [ADDR_MODE4_def] ``SND (ADDR_MODE4 P U base n)``
);

val LENGTH_ADDR_MODE4 = save_thm("LENGTH_ADDR_MODE4",
  (GEN_ALL o REWRITE_CONV [FST_ADDR_MODE4]) ``LENGTH (FST (ADDR_MODE4 P U base n))``
);

val REGISTER_LIST_STM_THM = save_thm("REGISTER_LIST_STM_THM",
  (GSYM o REWRITE_RULE [(GSYM o CONJUNCT2) RP_GEN_RP,GSYM FST_ADDR_MODE4]) SPEC_REGISTER_LIST_LEM
);

val LENGTH_ADDRESS_LIST =
  (GEN_ALL o REWRITE_CONV [LENGTH_GENLIST,ADDRESS_LIST_def]) ``LENGTH (ADDRESS_LIST base n)``;

val FST_HD_FST_ADDR_MODE4 = store_thm("FST_HD_FST_ADDR_MODE4",
  `!P U base n. 0 < LENGTH (REGISTER_LIST n) ==>
             (HD (FST (ADDR_MODE4 P U base n)) = RP stm n (ONECOMP 16 0))`,
  RW_TAC std_ss [FST_ADDR_MODE4,(GSYM o CONJUNCT1) EL,MASKN_ZERO,
                 LENGTH_ADDRESS_LIST,GSYM SPEC_REGISTER_LIST_LEM]
    THEN REWRITE_TAC [RP_GEN_RP]
);

(* -------------------------------------------------------- *)

val GEN_REG_LIST_NOT_LAST = prove(
  `!x y n. y < LENGTH (GEN_REG_LIST (SUC x) n) - 1 ==>
             ~(EL y (GEN_REG_LIST (SUC x) n) = x)`,
  RW_TAC arith_ss [LENGTH_SNOC,GEN_REG_LIST_THM,EL_SNOC]
    THENL [
      IMP_RES_TAC EL_GEN_REG_LIST_LT_WL
        THEN ASM_SIMP_TAC arith_ss [],
      `y < LENGTH (GEN_REG_LIST x n)` by DECIDE_TAC
        THEN IMP_RES_TAC EL_GEN_REG_LIST_LT_WL
        THEN ASM_SIMP_TAC arith_ss []
    ]
);

val RP_NOT_15 = store_thm("RP_NOT_15",
  `!ic y n. ((ic = ldm) \/ (ic = stm)) /\
            y < LENGTH (REGISTER_LIST n) - 1 ==>
            ~(RP ic n (MASKN 16 y n) = 15)`,
  RW_TAC bool_ss [] THEN REWRITE_TAC [RP_GEN_RP]
    THEN ASM_SIMP_TAC bool_ss [(SIMP_RULE std_ss [DECIDE (Term `x < y - 1 ==> x < y`),
     REGISTER_LIST_GEN_REG_LIST,REGISTER_LIST_LEM2] o SPEC `15`) GEN_REG_LIST_NOT_LAST]
);

val lem = DECIDE (Term `!x. 0 < x ==> (x - 1 < x) /\ (x = SUC (x - 1))`);

val GEN_RP_LAST = prove(
  `!x n. 0 < LENGTH (GEN_REG_LIST (SUC x) n) ==>
     ((EL (LENGTH (GEN_REG_LIST (SUC x) n) - 1) (GEN_REG_LIST (SUC x) n) = x) = BIT x n)`,
  RW_TAC arith_ss [LENGTH_SNOC,GEN_REG_LIST_THM,EL_SNOC,EL_LENGTH_SNOC]
    THEN PROVE_TAC [lem,prim_recTheory.LESS_NOT_EQ,EL_GEN_REG_LIST_LT_WL]
);

val RP_LAST_15 = prove(
  `!n. 0 < LENGTH (REGISTER_LIST n) ==>
         ((RP ldm n (MASKN 16 (LENGTH (REGISTER_LIST n) - 1) n) = 15) = BIT 15 n)`,
  RW_TAC bool_ss [RP_GEN_RP,
    (SIMP_RULE std_ss [lem,REGISTER_LIST_GEN_REG_LIST,REGISTER_LIST_LEM2] o SPEC `15`) GEN_RP_LAST]
);

val REG_WRITEN_COMMUTES = prove(
  `!n ireg reg m1 m2 i.
        n < LENGTH (REGISTER_LIST ireg) ==>
          (REG_WRITEN n (REG_WRITE reg m1 15 d) m2 ireg i =
           REG_WRITE (REG_WRITEN n reg m2 ireg i) m1 15 d)`,
  Induct THEN RW_TAC bool_ss [REG_WRITEN_def,REG_WRITE_RP_def]
    THEN `RP ldm ireg (MASKN 16 n ireg) < 16` by ASM_SIMP_TAC arith_ss [RP_LT_16]
    THEN `~(RP ldm ireg (MASKN 16 n ireg) = 15)` by ASM_SIMP_TAC arith_ss [RP_NOT_15]
    THEN ASM_SIMP_TAC arith_ss [REG_WRITE_RP_def,GSYM REG_WRITE_COMMUTE_PC]
);

val LENGTH_GEN_REG_LIST_NOT_ZERO = prove(
  `!wl ireg. BIT wl ireg ==> 0 < LENGTH (GEN_REG_LIST (SUC wl) ireg)`,
  RW_TAC arith_ss [REGISTER_LIST_LEM,SUM_def,BITV_THM,SBIT_def]
);

val LENGTH_REGISTER_LIST_NOT_ZERO =
  (SIMP_RULE arith_ss [REGISTER_LIST_GEN_REG_LIST] o SPEC `15`) LENGTH_GEN_REG_LIST_NOT_ZERO;

(* --- *)

val REG_WRITE_WRITEN_PC = prove(
  `!ireg reg mode i.  BIT 15 ireg ==>
      (REG_WRITEN (LENGTH (REGISTER_LIST ireg)) (REG_WRITE reg usr 15 d) mode ireg i =
       REG_WRITEN (LENGTH (REGISTER_LIST ireg)) reg mode ireg i)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LENGTH_REGISTER_LIST_NOT_ZERO
    THEN IMP_RES_TAC lem
    THEN POP_ASSUM SUBST1_TAC
    THEN FULL_SIMP_TAC bool_ss [GSYM RP_LAST_15]
    THEN ASM_SIMP_TAC arith_ss [REG_WRITEN_def,REG_WRITE_RP_def,REG_WRITEN_COMMUTES,
                                TO_WRITE_READ6,REG_WRITE_WRITE]
);

val REG_WRITEN_WRITE_PC = prove(
  `!ireg reg mode i.  BIT 15 ireg ==>
      (REG_WRITE (REG_WRITEN (LENGTH (REGISTER_LIST ireg)) reg mode ireg i) usr 15
                 (PROJ_DATA (i (LENGTH (REGISTER_LIST ireg) - 1))) =
       REG_WRITEN (LENGTH (REGISTER_LIST ireg)) reg mode ireg i)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LENGTH_REGISTER_LIST_NOT_ZERO
    THEN IMP_RES_TAC lem
    THEN POP_ASSUM SUBST1_TAC
    THEN FULL_SIMP_TAC bool_ss [GSYM RP_LAST_15]
    THEN ASM_SIMP_TAC arith_ss [REG_WRITEN_def,REG_WRITE_RP_def,TO_WRITE_READ6,REG_WRITE_WRITE]
);

val REG_WRITEN_WRITE_PC2 = prove(
  `!ireg reg mode i.  BIT 15 ireg ==>
      (REG_WRITE (REG_WRITEN (LENGTH (REGISTER_LIST ireg) - 1) reg mode ireg i) usr 15
                 (PROJ_DATA (i (LENGTH (REGISTER_LIST ireg) - 1))) =
       REG_WRITEN (LENGTH (REGISTER_LIST ireg)) reg mode ireg i)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LENGTH_REGISTER_LIST_NOT_ZERO
    THEN IMP_RES_TAC lem
    THEN POP_ASSUM SUBST1_TAC
    THEN FULL_SIMP_TAC bool_ss [GSYM RP_LAST_15]
    THEN ASM_SIMP_TAC arith_ss [REG_WRITEN_def,REG_WRITE_RP_def,TO_WRITE_READ6,REG_WRITE_WRITE]
);

val REG_READ_WRITEN_PC = prove(
  `!ireg reg mode i.  BIT 15 ireg ==>
      (REG_READ6 (REG_WRITEN (LENGTH (REGISTER_LIST ireg)) reg mode ireg i) usr 15 =
       (PROJ_DATA (i (LENGTH (REGISTER_LIST ireg) - 1))))`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC LENGTH_REGISTER_LIST_NOT_ZERO
    THEN IMP_RES_TAC lem
    THEN POP_ASSUM SUBST1_TAC
    THEN FULL_SIMP_TAC bool_ss [GSYM RP_LAST_15]
    THEN ASM_SIMP_TAC arith_ss [REG_WRITEN_def,REG_WRITE_RP_def,TO_WRITE_READ6,REG_READ_WRITE]
);

val REG_WRITEN_COMMUTE_PC = prove(
  `!ireg reg mode i.  ~BIT 15 ireg /\ 0 < LENGTH (REGISTER_LIST ireg) ==>
      (REG_WRITEN (LENGTH (REGISTER_LIST ireg)) (REG_WRITE reg usr 15 d) mode ireg i =
       REG_WRITE (REG_WRITEN (LENGTH (REGISTER_LIST ireg)) reg mode ireg i) usr 15 d)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC lem
    THEN POP_ASSUM SUBST1_TAC
    THEN FULL_SIMP_TAC bool_ss [GSYM RP_LAST_15]
    THEN ASM_SIMP_TAC arith_ss [REG_WRITEN_def,REG_WRITE_RP_def,REG_WRITEN_COMMUTES,
           REG_WRITE_COMMUTE_PC,RP_LT_16,lem]
);

(* --- *)

val REG_WRITE_READ_PC = save_thm("REG_WRITE_READ_PC",
  (GEN_ALL o SIMP_RULE arith_ss [TO_WRITE_READ6] o
   INST [`n2` |-> `15`] o SPEC_ALL) REG_WRITE_READ_NEQ
);

val REG_READ_WRITEN_PC2 = store_thm("REG_READ_WRITEN_PC2",
  `!ireg reg mode i.  x < LENGTH (REGISTER_LIST ireg) ==>
      (REG_READ6 (REG_WRITEN x reg mode ireg i) usr 15 = REG_READ6 reg usr 15)`,
  REPEAT STRIP_TAC
    THEN Induct_on `x`
    THEN REWRITE_TAC [REG_WRITEN_def]
    THEN STRIP_TAC THEN IMP_RES_TAC prim_recTheory.SUC_LESS
    THEN ASM_SIMP_TAC arith_ss [REG_WRITE_RP_def,RP_NOT_15,RP_LT_16,REG_WRITE_READ_PC]
);

val BIT_W32_NUM = GSYM WORD_BIT_def;
val RP_LAST_15 = save_thm("RP_LAST_15",
  (GEN_ALL o REWRITE_RULE [BIT_W32_NUM] o SPEC `w2n ireg`) RP_LAST_15);
val REG_WRITEN_COMMUTES = save_thm("REG_WRITEN_COMMUTES",
  (GEN_ALL o REWRITE_RULE [BIT_W32_NUM] o SPECL [`n`,`w2n ireg`]) REG_WRITEN_COMMUTES);
val REG_WRITE_WRITEN_PC = save_thm("REG_WRITE_WRITEN_PC",
  (GEN_ALL o REWRITE_RULE [BIT_W32_NUM] o SPEC `w2n ireg`) REG_WRITE_WRITEN_PC);
val REG_WRITEN_WRITE_PC = save_thm("REG_WRITEN_WRITE_PC",
  (GEN_ALL o REWRITE_RULE [BIT_W32_NUM] o SPEC `w2n ireg`) REG_WRITEN_WRITE_PC);
val REG_WRITEN_WRITE_PC2 = save_thm("REG_WRITEN_WRITE_PC2",
  (GEN_ALL o REWRITE_RULE [BIT_W32_NUM] o SPEC `w2n ireg`) REG_WRITEN_WRITE_PC2);
val REG_READ_WRITEN_PC = save_thm("REG_READ_WRITEN_PC",
  (GEN_ALL o REWRITE_RULE [BIT_W32_NUM] o SPEC `w2n ireg`) REG_READ_WRITEN_PC);
val REG_WRITEN_COMMUTE_PC = save_thm("REG_WRITEN_COMMUTE_PC",
  (GEN_ALL o REWRITE_RULE [BIT_W32_NUM] o SPEC `w2n ireg`) REG_WRITEN_COMMUTE_PC);

(* -------------------------------------------------------- *)

val PENCZ1 = prove(
   `!wl n x. x < LENGTH (GEN_REG_LIST wl n) ==> ~(BITWISE wl (/\) n (MASKN wl x n) = 0)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC EXISTS_SUM_BITS
    THEN POP_ASSUM SUBST_ALL_TAC
    THEN FULL_SIMP_TAC bool_ss [REGISTER_LIST_LEM]
    THEN IMP_RES_TAC SUM_LT
    THEN PAT_ASSUM `BITWISE wl $/\ n (MASKN wl (SUM p (BITV n)) n) = 0` SUBST_ALL_TAC
    THEN PROVE_TAC [BIT_ZERO]
);

val BITS_SUM = prove(
   `!h n. BITS h 0 n = SUM (SUC h) (\b. SLICE b b n)`,
   Induct THEN1 SIMP_TAC bool_ss [SYM ONE,SUM_1,SLICE_ZERO_THM]
     THEN ONCE_REWRITE_TAC [SUM_def]
     THEN RW_TAC arith_ss [BITS_SUC_THM,BIT_SLICE_THM]
);

val SPEC_MASKN_THM = (GEN_ALL o SIMP_RULE arith_ss [] o SPECL [`wl`,`wl`]) MASKN_THM;
val SPEC_SUM_ZERO = (GEN_ALL o BETA_RULE o SPECL [`SUC b`,`\x. SLICE x x a`]) SUM_ZERO;

val lem = prove(
  `!a b. a < 2 EXP b /\ (!c. c < b ==> ~BIT c a) ==> (a = 0)`,
  Cases_on `b` THEN1 SIMP_TAC arith_ss []
    THEN REPEAT STRIP_TAC
    THEN `!c. c < SUC n ==> (SLICE c c a = 0)` by PROVE_TAC [BIT_SLICE_THM3]
    THEN IMP_RES_TAC SPEC_SUM_ZERO
    THEN RULE_ASSUM_TAC (REWRITE_RULE [GSYM BITS_SUM,BITS_ZERO3])
    THEN PROVE_TAC [LESS_MOD]
);

val PENCZ2 = prove(
  `!wl n. BITWISE wl (/\) n (MASKN wl (LENGTH (GEN_REG_LIST wl n)) n) = 0`,
  REWRITE_TAC [REGISTER_LIST_LEM]
    THEN PROVE_TAC [REGISTER_LIST_LEM,BITWISE_LT_2EXP,SPEC_MASKN_THM,lem]
);

val PENCZ_THM = store_thm("PENCZ_THM",
  `!ic. ((ic = ldm) \/ (ic = stm)) ==>
         (!n x.  x < LENGTH (REGISTER_LIST n) ==>
            ~PENCZ ic n (MASKN 16 x n)) /\
          !n. PENCZ ic n (MASKN 16 (LENGTH (REGISTER_LIST n)) n)`,
  RW_TAC bool_ss [PENCZ_def,PENCZ2,PENCZ1,SYM REGISTER_LIST_GEN_REG_LIST]
);

val PENCZ_THM2 = store_thm("PENCZ_THM2",
  `!ireg. (WORD_BITS 15 0 ireg = 0) = (LENGTH (REGISTER_LIST (w2n ireg)) = 0)`,
  STRIP_TAC
    THEN STRUCT_CASES_TAC (SPEC `ireg` word_nchotomy)
    THEN SIMP_TAC arith_ss [WORD_BITS_def,GSYM REGISTER_LIST_GEN_REG_LIST,w2n_EVAL,
                            BITV_def,REGISTER_LIST_LEM,BITS_SUM,GSYM SUM_ZERO]
    THEN SIMP_TAC arith_ss [MOD_WL_THM,BITS_COMP_THM2,HB_def,GSYM BIT_SLICE_THM3,NOT_BIT]
);

val BITWISE_AND_ZERO = prove(
  `!n a. BITWISE n (/\) 0 a = 0`,
  Induct THEN1 REWRITE_TAC [BITWISE_def]
    THEN RW_TAC arith_ss [BITWISE_def,SBIT_def,BIT_ZERO]
);

val PENCZ_THM3 = store_thm("PENCZ_THM3",
  `!ireg mask. (WORD_BITS 15 0 ireg = 0) /\
               ((ic = ldm) \/ (ic = stm)) ==> PENCZ ic (w2n ireg) mask`,
  NTAC 2 STRIP_TAC
    THEN STRUCT_CASES_TAC (SPEC `ireg` word_nchotomy)
    THEN RW_TAC bool_ss [WORD_BITS_def,PENCZ_def,w2n_EVAL,MOD_WL_THM,numLib.num_CONV ``16``]
    THEN ONCE_REWRITE_TAC [GSYM BITWISE_BITS]
    THEN FULL_SIMP_TAC arith_ss [BITS_COMP_THM2,HB_def,BITWISE_AND_ZERO]
);

(* -------------------------------------------------------- *)

val ADD_THREE_ONE = prove(
  `!a. w32 3 + a + w32 1 = a + w32 4`,
  ONCE_REWRITE_TAC [WORD_ADD_COMM] THEN SIMP_TAC arith_ss [ADD_EVAL,WORD_ADD_ASSOC]
);

val WB_CALC = prove(
  `!x. 1 <= x ==> (w32 (4 * (x - 1) + 3) + a + w32 1 = a + w32 (4 * x))`,
  ONCE_REWRITE_TAC [WORD_ADD_COMM]
    THEN SIMP_TAC arith_ss [ADD_EVAL,WORD_ADD_ASSOC]
    THEN Induct_on `x` THEN RW_TAC arith_ss [MULT_CLAUSES]
);

val WB_CALC2 = DECIDE (Term `!x. 1 <= x ==> (4 * (x - 1) = 4 * x - 4)`);

val REGISTER_LIST_LENGTH = 
  (GSYM o REWRITE_RULE [RP_GEN_RP,REGISTER_LIST_GEN_REG_LIST] o SPEC `16`) REGISTER_LIST_LEM;

val FIRST_ADDRESS = store_thm("FIRST_ADDRESS",
  `!i ic base c borrow2 mul.
    1 <= LENGTH (REGISTER_LIST (w2n i)) /\ ((ic = ldm) \/ (ic = stm)) ==>
    (FIRST_ADDRESS (WORD_BIT 24 i) (WORD_BIT 23 i) base
      (WB_ADDRESS (WORD_BIT 23 i) base (LENGTH (REGISTER_LIST (w2n i)))) =
     SND (ALU6 ic t3 i borrow2 mul F (OFFSET ic t3 i (WORD_BITS 15 0 i)) base c))`,
  RW_TAC std_ss [iseq_distinct,FIRST_ADDRESS_def,WB_ADDRESS_def,ALU6_def,OFFSET_def,
                 ALUOUT_ADD_CARRY,ALUOUT_ADD,ALUOUT_ALU_logic,bitsTheory.SBIT_def,UP_DOWN_def,
                 REGISTER_LIST_LENGTH,REGISTER_LIST_WORD150,ADD_THREE_ONE,WORD_ADD_0,GSYM WORD_SUB_SUB,
                 GSYM WORD_ADD_SUB_SYM,NOT_ADD_1]
   THEN ASM_SIMP_TAC arith_ss [NOT_ADD,ADD_EVAL,WB_CALC2,
             SIMP_RULE arith_ss [LT_WL_def,HB_def,WL_def] WORD_SUB_LT_EQ]
);

val WB_ADDRESS = store_thm("WB_ADDRESS",
  `!i ic base c borrow2 mul. ((ic = ldm) \/ (ic = stm)) ==>
    (WB_ADDRESS (WORD_BIT 23 i) base (LENGTH (REGISTER_LIST (w2n i))) =
     SND (ALU6 ic t4 i borrow2 mul F (OFFSET ic t4 i (WORD_BITS 15 0 i)) base c))`,
  RW_TAC arith_ss [iseq_distinct,FIRST_ADDRESS_def,WB_ADDRESS_def,ALU6_def,OFFSET_def,
                   ALUOUT_ADD_CARRY,ALUOUT_ADD,ALUOUT_ALU_logic,bitsTheory.SBIT_def,UP_DOWN_def,
                   REGISTER_LIST_LENGTH,REGISTER_LIST_WORD150,ADD_THREE_ONE,WORD_ADD_0,GSYM WORD_SUB_SUB,
                   GSYM WORD_ADD_SUB_SYM,NOT_ADD_1,PENCZ_THM2]
   THEN ASM_SIMP_TAC arith_ss [NOT_ADD,ADD_EVAL,WB_CALC,WB_CALC2,WORD_SUB_RZERO,
             SIMP_RULE arith_ss [LT_WL_def,HB_def,WL_def] WORD_SUB_LT_EQ]
);

val WB_ADDRESS_ZERO = save_thm("WB_ADDRESS_ZERO",
  (GEN_ALL o SIMP_RULE bool_ss [(GEN_ALL o snd o EQ_IMP_RULE o SPEC_ALL) PENCZ_THM2] o
   DISCH `LENGTH (REGISTER_LIST (w2n i)) = 0` o GSYM o SPEC_ALL) WB_ADDRESS
);

(* -------------------------------------------------------- *)

val PENCZ_RP_150 = store_thm("PENCZ_RP_150",
  `!ic.
   (!ireg mask. PENCZ ic (WORD_BITS 15 0 ireg) mask = PENCZ ic (w2n ireg) mask) /\
   (!ireg mask. RP ic (WORD_BITS 15 0 ireg) mask = RP ic (w2n ireg) mask)`,
  REPEAT STRIP_TAC
    THEN STRUCT_CASES_TAC (SPEC `ireg` word_nchotomy)
    THEN SIMP_TAC arith_ss [PENCZ_def,RP_def,w2n_EVAL,MOD_WL_THM,WORD_BITS_def,
                            HB_def,BITS_COMP_THM2]
    THEN REWRITE_TAC [numLib.num_CONV ``16``]
    THEN ONCE_REWRITE_TAC [GSYM BITWISE_BITS]
    THEN SIMP_TAC arith_ss [BITS_COMP_THM2]
);

val MASK_BIT_150 = prove(
  `!ireg. MASK_BIT 16 (WORD_BITS 15 0 ireg) = MASK_BIT 16 (w2n ireg)`,
  REWRITE_TAC [FUN_EQ_THM,MASK_BIT_def,(SYM o CONJUNCT1) RP_GEN_RP,PENCZ_RP_150]
);

val MASKN_150 = store_thm("MASKN_150",
  `!ireg x. MASKN 16 x (WORD_BITS 15 0 ireg) = MASKN 16 x (w2n ireg)`,
  REWRITE_TAC [MASKN_def,MASK_BIT_150]
);

val MASKN16_1 = store_thm("MASKN16_1",
  `!ic ireg. ((ic = ldm) \/ (ic = stm)) ==>
      (CLEARBIT 16 (RP ic ireg (ONECOMP 16 0)) (ONECOMP 16 0) = MASKN 16 1 ireg)`,
  RW_TAC arith_ss [MASKN_def,MASK_BIT_def,CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV FUNPOW]
    THEN REWRITE_TAC [RP_GEN_RP]
);

val MASKN16_2 = store_thm("MASKN16_2",
  `!ic ireg. ((ic = ldm) \/ (ic = stm)) ==>
       (CLEARBIT 16
           (RP ic ireg
              (CLEARBIT 16 (RP ic ireg (ONECOMP 16 0)) (ONECOMP 16 0)))
           (CLEARBIT 16 (RP ic ireg (ONECOMP 16 0)) (ONECOMP 16 0)) =
        MASKN 16 2 ireg)`,
  RW_TAC arith_ss [MASKN_def,MASK_BIT_def,CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV FUNPOW]
    THEN REWRITE_TAC [RP_GEN_RP]
);

val MASKN16_2b = save_thm("MASKN16_2b",
  (SIMP_RULE stdi_ss [SPEC `stm` MASKN16_1] o SPEC `stm`) MASKN16_2
);

val MASKN_SUC = prove(
  `!ic ireg. ((ic = ldm) \/ (ic = stm)) ==>
       (CLEARBIT 16 (RP ic ireg (MASKN 16 n ireg)) (MASKN 16 n ireg) =
        MASKN 16 (SUC n) ireg)`,
   RW_TAC bool_ss [] THEN REWRITE_TAC [RP_GEN_RP,(REWRITE_RULE [GSYM MASKN_def] o
     REWRITE_RULE [FUNPOW_SUC,MASK_BIT_def] o SPECL [`16`,`SUC n`]) MASKN_def]
);

(* -------------------------------------------------------- *)

val LDM_LIST_EMPTY = store_thm("LDM_LIST_EMPTY",
  `!reg mode. LDM_LIST reg mode [] [] = reg`,
  SIMP_TAC list_ss [LDM_LIST_def]
);

(* -------------------------------------------------------- *)

val IS_ABORT_LEM = store_thm("IS_ABORT_LEM",
  `!i t. IS_ABORT i t = FST (SND (i t))`,
  NTAC 2 STRIP_TAC
    THEN Cases_on `i t` THEN Cases_on `r` THEN Cases_on `r'` THEN Cases_on `r`
    THEN FULL_SIMP_TAC std_ss [IS_ABORT_def,PROJ_ABORT_def]
);

(* -- *)

val IS_ABORT_ZERO = prove(
  `(?s. s < 1 /\ IS_ABORT i (s + 1)) = IS_ABORT i 1`,
  EQ_TAC THEN REPEAT STRIP_TAC
    THENL [
      `s = 0` by DECIDE_TAC THEN FULL_SIMP_TAC arith_ss [],
      EXISTS_TAC `0` THEN ASM_SIMP_TAC arith_ss []
    ]
);

val LEAST_ABORT_ZERO = prove(
  `!w i. 0 < w /\ IS_ABORT i 1 ==> ((LEAST s. s < w /\ IS_ABORT i (s + 1)) = 0)`,
   REPEAT STRIP_TAC
     THEN REWRITE_TAC [LEAST_DEF]
     THEN ONCE_REWRITE_TAC [WHILE]
     THEN ASM_SIMP_TAC arith_ss []
);

val LEAST_ABORT_ZERO_ISA = prove(
  `!i. IS_ABORT i 1 ==> ((LEAST s. IS_ABORT i (s + 1)) = 0)`,
   REPEAT STRIP_TAC
     THEN REWRITE_TAC [LEAST_DEF]
     THEN ONCE_REWRITE_TAC [WHILE]
     THEN RW_TAC arith_ss []
     THEN ONCE_REWRITE_TAC [WHILE]
     THEN ASM_SIMP_TAC arith_ss []
);

val lem = prove(
  `(!m. m < n ==> ~(m < w /\ IS_ABORT i (m + 1))) /\ n < w /\ IS_ABORT i (n + 1) ==>
          (n = LEAST s. IS_ABORT i (s + 1))`,
  RW_TAC std_ss []
    THEN `!m. m < n ==> m < w` by metisLib.METIS_TAC [LESS_TRANS]
    THEN FULL_SIMP_TAC std_ss [(BETA_RULE o INST [`P` |-> `\s. IS_ABORT i (s + 1)`]) LEAST_THM]
);

val LEAST_ABORT_ISA = prove(
  `(?s. s < w /\ IS_ABORT i (s + 1)) ==>
    ((LEAST s. s < w /\ IS_ABORT i (s + 1)) = (LEAST s. IS_ABORT i (s + 1)))`,
  RW_TAC std_ss []
    THEN IMP_RES_TAC ((GEN_ALL o BETA_RULE o
           SPECL [`\l. l = LEAST s. IS_ABORT i (s + 1)`,`\s. s < w /\ IS_ABORT i (s + 1)`]) LEAST_ELIM)
    THEN metisLib.METIS_TAC [lem]
);

val LEAST_ABORT_LT2 = prove(
  `(?s. s < w /\ IS_ABORT i (s + 1)) ==> (LEAST s. IS_ABORT i (s + 1)) < w`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC (GSYM LEAST_ABORT_ISA)
    THEN POP_ASSUM SUBST1_TAC
    THEN metisLib.METIS_TAC [lem,(GEN_ALL o SIMP_RULE bool_ss [] o
                      BETA_RULE o SPECL [`\l. l < w`,`\s. s < w /\ IS_ABORT i (s + 1)`]) LEAST_ELIM]
);

val LEAST_ABORT_ZERO_ISA = save_thm("LEAST_ABORT_ZERO_ISA",
  REWRITE_RULE [IS_ABORT_LEM] LEAST_ABORT_ZERO_ISA
);

val LEAST_ABORT_ISA = save_thm("LEAST_ABORT_ISA",
  (GEN_ALL o REWRITE_RULE [IS_ABORT_LEM]) LEAST_ABORT_ISA
);

val LEAST_ABORT_LT2 = save_thm("LEAST_ABORT_LT2",
  REWRITE_RULE [IS_ABORT_LEM] LEAST_ABORT_LT2
);

(* -------------------------------------------------------- *)

val NEW_ABORT_SUC = prove(
  `!x. (?s. s < x + 1 /\ IS_ABORT i (s + 1)) \/ IS_ABORT i (x + 2) =
        ?s. s < x + 2 /\ IS_ABORT i (s + 1)`,
  STRIP_TAC THEN EQ_TAC THEN RW_TAC arith_ss []
    THEN1 metisLib.METIS_TAC [DECIDE ``!s x. s < x + 1 ==> s < x + 2``]
    THENL [
      EXISTS_TAC `x + 1` THEN ASM_SIMP_TAC arith_ss [],
      Cases_on `s = x + 1` THEN1 FULL_SIMP_TAC arith_ss []
        THEN DISJ1_TAC THEN EXISTS_TAC `s`
        THEN ASM_SIMP_TAC arith_ss []
    ]
);

val lem = prove(
  `!w x i. SUC x <= w - 1 /\ (!s. s < x + 1 ==> ~IS_ABORT i (s + 1)) /\ s < x + 2 /\ IS_ABORT i (s + 1) ==>
       (!n. (!m. m < n ==> m < w ==> ~IS_ABORT i (m + 1)) /\
             n < w /\ IS_ABORT i (n + 1) ==> (n = x + 1))`,
  RW_TAC std_ss []
    THEN Cases_on `n < x + 1`
    THEN1 PAT_ASSUM `!s. s < w ==> ~IS_ABORT i (s + 1)` (SPEC_THEN `n` IMP_RES_TAC)
    THEN Tactical.REVERSE (Cases_on `x + 1 < n`)
    THEN1 DECIDE_TAC
    THEN `s < n` by DECIDE_TAC
    THEN `s < w` by DECIDE_TAC
    THEN PAT_ASSUM `!m. m < n ==> m < w ==> ~IS_ABORT i (m + 1)` (SPEC_THEN `s` IMP_RES_TAC)
);

val NEW_LEAST_ABORT_SUC = prove(
  `!x w i s. SUC x <= w - 1 /\ (!s. s < x + 1 ==> ~IS_ABORT i (s + 1)) /\ s < x + 2 /\ IS_ABORT i (s + 1) ==>
           ((LEAST s. s < w /\ IS_ABORT i (s + 1)) = x + 1)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC lem
    THEN `s < w` by DECIDE_TAC
    THEN IMP_RES_TAC ((GEN_ALL o REWRITE_RULE [DECIDE ``!a b c. a /\ b ==> c = (a ==> b ==> c)``,
                                               DECIDE ``!a b. ~(a /\ b) = (a ==> ~b)``] o
             BETA_RULE o SPECL [`\l. l = x + 1`,`\s. s < w /\ IS_ABORT i (s + 1)`]) LEAST_ELIM)
);

val NEW_LEAST_ABORT_ZERO = prove(
  `!w i. 0 < w /\ (?s. s < 1 /\ IS_ABORT i (s + 1)) ==> ((LEAST s. s < w /\ IS_ABORT i (s + 1)) = 0)`,
   REPEAT STRIP_TAC
     THEN `s = 0 ` by DECIDE_TAC
     THEN REWRITE_TAC [LEAST_DEF]
     THEN ONCE_REWRITE_TAC [WHILE]
     THEN FULL_SIMP_TAC arith_ss []
);

val lem = prove(
  `!w x i. 1 < w /\ x < w - 1 /\ IS_ABORT i (x + 1) ==>
       (!n. (!m. m < n ==> m < w ==> ~IS_ABORT i (m + 1)) /\
             n < w /\ IS_ABORT i (n + 1) ==> (n < w))`,
  RW_TAC arith_ss []
);

val NEW_LEAST_ABORT_LT = prove(
  `!x w i. 1 < w /\ x < w - 1 /\ IS_ABORT i (x + 1) ==>
           ((LEAST s. s < w /\ IS_ABORT i (s + 1)) < w)`,
  metisLib.METIS_TAC [lem,DECIDE ``x < w - 1 ==> x < w``,
                      (GEN_ALL o REWRITE_RULE [DECIDE ``!a b. ~(a /\ b) = (a ==> ~b)``] o
                       BETA_RULE o SPECL [`\l. l < w`,`\s. s < w /\ IS_ABORT i (s + 1)`]) LEAST_ELIM]
);

val NEW_LEAST_ABORT_LT2 = prove(
  `!x w i. 1 < w /\ x < w - 1 /\ IS_ABORT i (x + 1) ==>
           ((LEAST s. s < w /\ IS_ABORT i (s + 1)) - 1 < w)`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC NEW_LEAST_ABORT_LT THEN DECIDE_TAC
);

val lem = prove(
  `!w x i. 1 < w /\ x < w /\ IS_ABORT i (x + 1) ==>
       (!n. (!m. m < n ==> m < w ==> ~IS_ABORT i (m + 1)) /\
             n < w /\ IS_ABORT i (n + 1) ==> (n - 1 < w))`,
  RW_TAC arith_ss []
);

val NEW_LEAST_ABORT_LT3 = prove(
  `!x w i. 1 < w /\ x < w /\ IS_ABORT i (x + 1) ==>
           ((LEAST s. s < w /\ IS_ABORT i (s + 1)) - 1 < w)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC lem
    THEN metisLib.METIS_TAC [(GEN_ALL o REWRITE_RULE [DECIDE ``!a b. ~(a /\ b) = (a ==> ~b)``] o
                             BETA_RULE o SPECL [`\l. l - 1 < w`,`\s. s < w /\ IS_ABORT i (s + 1)`]) LEAST_ELIM]
);

val NEW_ABORT_SUC = REWRITE_RULE [IS_ABORT_LEM] NEW_ABORT_SUC;
val NEW_LEAST_ABORT_SUC = REWRITE_RULE [IS_ABORT_LEM] NEW_LEAST_ABORT_SUC;
val NEW_LEAST_ABORT_ZERO = REWRITE_RULE [IS_ABORT_LEM] NEW_LEAST_ABORT_ZERO;
val NEW_LEAST_ABORT_LT = REWRITE_RULE [IS_ABORT_LEM] NEW_LEAST_ABORT_LT;
val NEW_LEAST_ABORT_LT2 = REWRITE_RULE [IS_ABORT_LEM] NEW_LEAST_ABORT_LT2;
val NEW_LEAST_ABORT_LT3 = REWRITE_RULE [IS_ABORT_LEM] NEW_LEAST_ABORT_LT3;

(* -------------------------------------------------------- *)

fun SIMP_ASSUM a = (SIMP_RULE stdi_ss [COND_PAIR,MASKN16_2,MASKN16_1,PENCZ_THM3] o DISCH a);

val REG_WRITEN_SUC = save_thm("REG_WRITEN_SUC",
  (GEN_ALL o SIMP_RULE arith_ss [io_onestepTheory.ADVANCE_def,PROJ_DATA_def] o
   ONCE_REWRITE_RULE [form_4tuple] o INST [`i` |-> `ADVANCE 1 i`] o SPEC_ALL o
   REWRITE_RULE [REG_WRITE_RP_def] o GSYM o CONJUNCT2) REG_WRITEN_def
);

val PROJ_DATA = save_thm("PROJ_DATA",
  (GEN_ALL o CONV_RULE (RHS_CONV (REWRITE_CONV [PROJ_DATA_def])) o
   ONCE_REWRITE_CONV [form_4tuple]) ``PROJ_DATA x``);

val lem = prove(
  `!b. ~((if b then tm else tn) = t3)`,
  PROVE_TAC [iseq_distinct]
);

val NEXT_CORE_LDM_TN1 = (GEN_ALL o
   SIMP_ASSUM `~(WORD_BITS 15 0 ireg = 0)` o
   GEN_REWRITE_RULE (RAND_CONV o DEPTH_CONV) empty_rewrites
   [MULT_ADD_FOUR,MULT_ADD_FOUR2,PENCZ_RP_150,(SIMP_RULE bool_ss [iclass_distinct] o SPEC `ldm`) MASKN_SUC,
    GSYM WORD_BITS_def,ALUOUT_ALU_logic,LSL_ZERO,lem] o LDM_ITER_CONV)
   ``NEXT_ARM6 (ARM6 (DP (REG_WRITEN y reg
                          (if WORD_BIT 22 ireg /\ ~WORD_BIT 15 ireg then usr else
                           DECODE_MODE (WORD_BITS 4 0 (CPSR_READ psr)))
                          (w2n ireg) din)
                     psr (base + w32 (SUC x) * w32 4) din2 alua alub dout)
                   (CTRL pipea T pipeb T ireg T ointstart F F obaselatch F ldm tn
                     T F F onfq ooonfq oniq oooniq pipeaabt pipebabt pipebabt dataabt2
                     aregn2 T T F sctrlreg psrfb oareg
                     (MASKN 16 (SUC (SUC x)) (w2n ireg))
                     (RP ldm (w2n (ireg)) (MASKN 16 (SUC x) (w2n ireg)))
                     (RP ldm (w2n (ireg)) (MASKN 16 x (w2n ireg))) mul mul2 borrow2 mshift))
                 (NRESET,ABORT,NFQ,NIQ,DATA)``;

val LDM_PENCZ_THM = (GEN_ALL o SIMP_RULE std_ss [] o DISCH `LENGTH (REGISTER_LIST ireg) = x` o
                     SPEC `ireg` o CONJUNCT2 o SIMP_RULE stdi_ss [] o SPEC `ldm`) PENCZ_THM;

val LDM_PENCZ_LEM = prove(
  `!ireg x. SUC x <= LENGTH (REGISTER_LIST ireg) - 1 ==>
            (PENCZ ldm ireg (MASKN 16 (x + 2) ireg) = (x + 1 = LENGTH (REGISTER_LIST ireg) - 1))`,
  RW_TAC std_ss [GSYM ADD1]
    THEN Cases_on `SUC x  = LENGTH (REGISTER_LIST ireg) - 1`
    THENL [
      `LENGTH (REGISTER_LIST ireg) = x + 2` by DECIDE_TAC
        THEN ASM_SIMP_TAC arith_ss [LDM_PENCZ_THM],
      ASM_SIMP_TAC arith_ss [PENCZ_THM]]
);

val NEXT_CORE_LDM_TN_X = store_thm("NEXT_CORE_LDM_TN_X",
   `!x w reg ireg alub alua din dout i.
      (w = LENGTH (REGISTER_LIST (w2n ireg))) ==>
      0 < w ==>
      x <= w - 1 ==>
      (!t. t < SUC w ==> FST (i t)) ==>
      ?ointstart' onfq' ooonfq' oniq' oooniq' pipeaabt' pipebabt' aregn' oareg' mul' mul2' borrow2' mshift'.
        ~(num2exception aregn' IN {reset; undefined; software; address}) /\ (aregn' < 8) /\
        ((num2exception aregn' = fast) ==> ~WORD_BIT 6 (CPSR_READ psr)) /\
        ((num2exception aregn' = interrupt) ==> ~WORD_BIT 7 (CPSR_READ psr)) /\
       (FUNPOW (SNEXT NEXT_ARM6) x <|state := ARM6
                 (DP reg psr (if w = 1 then din else base + w32 1 * w32 4) (PROJ_DATA (i 1)) alua alub dout)
                 (CTRL pipea T pipeb T ireg T ointstart F F T F ldm (if w = 1 then tm else tn)
                    (~(w = 1)) F F onfq ooonfq oniq oooniq pipeaabt pipebabt pipebabt (IS_ABORT i 1)
                    aregn2 (~(w = 1)) T F sctrlreg psrfb oareg (MASKN 16 2 (w2n ireg))
                    (RP ldm (w2n (ireg)) (MASKN 16 1 (w2n ireg)))
                    (RP ldm (w2n (ireg)) (ONECOMP 16 0)) mul mul2 borrow2 mshift); inp := ADVANCE 2 i|> =
        (let dataabt2 = ?s. (s < x + 1) /\ IS_ABORT i (s + 1) in
         let y = if dataabt2 then LEAST s. (s < w) /\ IS_ABORT i (s + 1) else x
         and nbs = if WORD_BIT 22 ireg /\ ~WORD_BIT 15 ireg then usr
                   else DECODE_MODE (WORD_BITS 4 0 (CPSR_READ psr)) in
         <| state := ARM6 (DP (REG_WRITEN y reg nbs (w2n ireg) (ADVANCE 1 i)) psr
                   (if (x = w - 1) /\ ~(w = 1) then
                      REG_READ6 (REG_WRITEN (y - 1) reg nbs (w2n ireg) (ADVANCE 1 i)) usr 15
                     else if w = 1 then din else base + w32 (SUC x) * w32 4)
                    (PROJ_DATA (i (x + 1)))
                    (if x = 0 then alua else REG_READ6 reg nbs (WORD_BITS 19 16 ireg))
                    (if x = 0 then alub else PROJ_DATA (i x))
                    (if x = 0 then dout else PROJ_DATA (i x)))
                (CTRL pipea T pipeb T ireg T ointstart' F F (x = 0) F ldm (if x = w - 1 then tm else tn)
                    (~(x = w - 1)) F F onfq' ooonfq' oniq' oooniq' pipeaabt' pipebabt' pipebabt' dataabt2
                    (if x = 0 then aregn2 else if ointstart' then (if dataabt2 then 4 else aregn') else 2)
                    (~(x = w - 1)) T F sctrlreg (if x = 0 then psrfb else SPSR_READ psr nbs)
                    (if x = 0 then oareg else oareg') (MASKN 16 (SUC (SUC x)) (w2n ireg))
                    (RP ldm (w2n ireg) (MASKN 16 (SUC x) (w2n ireg)))
                    (RP ldm (w2n ireg) (MASKN 16 x (w2n ireg)))
                    mul' mul2' borrow2' mshift'); inp := ADVANCE x (ADVANCE 2 i)|>))`,
  Induct
    THEN1 (RW_TAC arith_ss [FUNPOW,REG_WRITEN_def,MASKN_ZERO,io_onestepTheory.ADVANCE_ZERO,
                            IS_ABORT_ZERO,LEAST_ABORT_ZERO] THEN FULL_SIMP_TAC arith_ss [interrupt_exists])
    THEN REPEAT STRIP_TAC
    THEN `1 < w /\ x <= w - 1` by DECIDE_TAC
    THEN PAT_ASSUM `!w reg alub alua din dout i. X` IMP_RES_TAC
    THEN POP_ASSUM (SPECL_THEN [`reg`,`dout`,`din`,`alub`,`alua`] STRIP_ASSUME_TAC)
    THEN FULL_SIMP_TAC arith_ss [FUNPOW_SUC]
    THEN POP_ASSUM (K ALL_TAC)
    THEN `~(WORD_BITS 15 0 ireg = 0)` by ASM_SIMP_TAC arith_ss [PENCZ_THM2]
    THEN PURE_REWRITE_TAC [SNEXT_NEXT_ARM6,pairTheory.FST,pairTheory.SND]
    THEN ASM_SIMP_TAC (arith_ss++STATE_INP_ss) [NEXT_CORE_LDM_TN1,PROJ_DATA,state_arm6_11,dp_11,ctrl_11,ADD1,
           IS_ABORT_LEM,NEW_ABORT_SUC,io_onestepTheory.ADVANCE_def,GSYM io_onestepTheory.ADVANCE_COMP,LDM_PENCZ_LEM,
           DECIDE ``!a b. (~a \/ b) = (a ==> b)``,NEW_LEAST_ABORT_ZERO,CONJUNCT1 REG_WRITEN_def,BIT_W32_NUM]
    THEN SIMP_TAC (bool_ss++boolSimps.CONJ_ss) [REG_WRITEN_SUC]
    THEN ONCE_REWRITE_TAC [DECIDE ``a /\ b /\ c /\ d /\ e /\ f /\ g /\ h =
                                   (a /\ b /\ c /\ d /\ h) /\ (e /\ f /\ g)``]
    THEN CONV_TAC EXISTS_AND_CONV
    THEN CONJ_TAC
    THENL [
      RW_TAC arith_ss [AREGN1_def,num2exception_thm,exception_distinct,exception_distinct,
                       pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY,
                       ONCE_REWRITE_RULE [DISJ_COMM] NEW_ABORT_SUC]
        THEN EXISTS_TAC `3`
        THEN SIMP_TAC std_ss [num2exception_thm,exception_distinct]
        THEN metisLib.METIS_TAC [NEW_ABORT_SUC],
      CONJ_TAC 
        THENL [
           RW_TAC std_ss [ADD1]
             THEN FULL_SIMP_TAC arith_ss [DECIDE ``!a b. (~a \/ b) = (a ==> b)``]
             THEN TRY (metisLib.METIS_TAC [DECIDE ``!s. s < x + 1 ==> s < x + 2``,NEW_LEAST_ABORT_SUC]),
           CONJ_TAC
             THENL [
               RW_TAC arith_ss [NEW_LEAST_ABORT_LT,NEW_LEAST_ABORT_LT2,NEW_LEAST_ABORT_LT3,REG_READ_WRITEN_PC2],
               RW_TAC arith_ss [RP_NOT_15] THEN metisLib.METIS_TAC []
             ]
        ]
    ]
);

val NEXT_CORE_LDM_TN_W1 = save_thm("NEXT_CORE_LDM_TN_W1",
  (GEN_ALL o SIMP_RULE arith_ss
    [WORD_MULT_CLAUSES,IS_ABORT_LEM,DECIDE ``!x. 1 < x ==> (SUC (x - 1) = x)``,
     DECIDE ``!w. 0 < w ==> (w <= 1 = (w = 1))``,GSYM io_onestepTheory.ADVANCE_COMP,
     WORD_ADD_0,PROJ_DATA] o
   INST [`w` |-> `LENGTH (REGISTER_LIST (w2n ireg))`] o
   SPEC_ALL o SPECL [`w - 1`,`w`]) NEXT_CORE_LDM_TN_X);

(* -------------------------------------------------------- *)

val NEXT_CORE_STM_TN1 = (GEN_ALL o
   SIMP_RULE stdi_ss [COND_PAIR] o
   GEN_REWRITE_RULE (RAND_CONV o DEPTH_CONV) empty_rewrites
   [MULT_ADD_FOUR,MULT_ADD_FOUR2,PENCZ_RP_150,(SIMP_RULE bool_ss [iclass_distinct] o SPEC `stm`) MASKN_SUC,
    GSYM WORD_BITS_def] o STM_ITER_CONV)
   ``NEXT_ARM6 (ARM6 (DP reg psr (base + w32 (SUC x) * w32 4) din alua alub dout)
                   (CTRL pipea T pipeb T ireg T ointstart F F obaselatch F stm tn
                     T F F onfq ooonfq oniq oooniq pipeaabt pipebabt pipebabt dataabt2
                     aregn2 T T T sctrlreg psrfb oareg
                     (MASKN 16 (SUC (SUC x)) (w2n ireg))
                     (RP stm (w2n (ireg)) (MASKN 16 (SUC x) (w2n ireg)))
                     (RP stm (w2n (ireg)) (MASKN 16 x (w2n ireg))) mul mul2 borrow2 mshift))
               (NRESET,ABORT,NFQ,NIQ,DATA)``;

val NEXT_CORE_STM_TN_X = store_thm("NEXT_CORE_STM_TN_X",
   `!x w y reg ireg alub alua dout i.
      (w = LENGTH (REGISTER_LIST (w2n ireg))) ==>
      1 < w ==>
      x <= w - 2 ==>
      (!t. t < SUC w ==> FST (i t)) ==>
      ?ointstart' obaselatch' onfq' ooonfq' oniq' oooniq' pipeaabt' pipebabt' dataabt2' aregn' oareg' mul' mul2' borrow2' mshift'.
        ~(num2exception aregn' IN {reset; undefined; software; address}) /\ (aregn' < 8) /\
        ((num2exception aregn' = fast) ==> ~WORD_BIT 6 (CPSR_READ psr)) /\
        ((num2exception aregn' = interrupt) ==> ~WORD_BIT 7 (CPSR_READ psr)) /\
       (FUNPOW (SNEXT NEXT_ARM6) x <|state := ARM6 (DP reg psr (base + w32 1 * w32 4) din alua alub dout)
                (CTRL pipea T pipeb T ireg T ointstart F F obaselatch F stm tn
                   T F F onfq ooonfq oniq oooniq pipeaabt pipebabt pipebabt dataabt2
                   aregn2 T T T sctrlreg psrfb oareg (MASKN 16 2 (w2n ireg))
                   (RP stm (w2n (ireg)) (MASKN 16 1 (w2n ireg)))
                   (RP stm (w2n (ireg)) (ONECOMP 16 0)) mul mul2 borrow2 mshift); inp := ADVANCE 2 i|> =
       (let nbs = if WORD_BIT 22 ireg then usr else DECODE_MODE (WORD_BITS 4 0 (CPSR_READ psr)) in
        <|state := ARM6 (DP reg psr (base + w32 (SUC x) * w32 4) (if x = 0 then din else ireg) alua alub
                 (if x = 0 then dout else REG_READ6 reg nbs (RP stm (w2n ireg) (MASKN 16 x (w2n ireg)))))
              (CTRL pipea T pipeb T ireg T ointstart' F F obaselatch' F stm tn
                 T F F onfq' ooonfq' oniq' oooniq' pipeaabt' pipebabt' pipebabt' dataabt2'
                 (if x = 0 then aregn2 else if ointstart' then aregn' else 2) T T T sctrlreg
                 (if x = 0 then psrfb else SPSR_READ psr nbs) (if x = 0 then oareg else oareg')
                 (MASKN 16 (SUC (SUC x)) (w2n ireg))
                 (RP stm (w2n ireg) (MASKN 16 (SUC x) (w2n ireg)))
                 (RP stm (w2n ireg) (MASKN 16 x (w2n ireg)))
                 mul' mul2' borrow2' mshift'); inp := ADVANCE x (ADVANCE 2 i)|>))`,
  Induct
    THEN1 (RW_TAC arith_ss [FUNPOW,MASKN_ZERO,GSYM io_onestepTheory.ADVANCE_COMP]
             THEN METIS_TAC [interrupt_exists])
    THEN REPEAT STRIP_TAC
    THEN `x <= w - 2` by DECIDE_TAC
    THEN PAT_ASSUM `!w y reg ireg alub alua dout i. X` IMP_RES_TAC
    THEN POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL)
    THEN FULL_SIMP_TAC std_ss [FUNPOW_SUC]
    THEN POP_ASSUM (K ALL_TAC)
    THEN `SUC (SUC x) < LENGTH (REGISTER_LIST (w2n ireg))` by DECIDE_TAC
    THEN `~(WORD_BITS 15 0 ireg = 0)` by ASM_SIMP_TAC arith_ss [PENCZ_THM2]
    THEN ABBREV_TAC `nbs = if WORD_BIT 22 ireg then usr else DECODE_MODE (WORD_BITS 4 0 (CPSR_READ psr))`
    THEN PURE_REWRITE_TAC [SNEXT_NEXT_ARM6,pairTheory.FST,pairTheory.SND]
    THEN ASM_SIMP_TAC (arith_ss++STATE_INP_ss) [PENCZ_THM,NEXT_CORE_STM_TN1,GSYM io_onestepTheory.ADVANCE_COMP,
                                DECIDE ``!x. x + 3 = SUC x + 2``,BIT_W32_NUM]
    THEN RW_TAC arith_ss [MASK_def,MASKN_SUC,io_onestepTheory.ADVANCE_def,
                          AREGN1_def,pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY]
    THEN FULL_SIMP_TAC arith_ss [num2exception_thm,exception_distinct]
    THEN METIS_TAC [SIMP_RULE (std_ss++pred_setSimps.PRED_SET_ss) [] interrupt_exists]
);

val NEXT_CORE_STM_TN_W2 =
  (GEN_ALL o SIMP_RULE arith_ss [] o
   INST [`w` |-> `LENGTH (REGISTER_LIST (w2n ireg))`] o
   SPEC_ALL o SPECL [`w - 2`,`w`]) NEXT_CORE_STM_TN_X;

val SUC_SUC_SUB2 = DECIDE (Term `!x. 1 < x ==> (SUC (SUC (x - 2)) = x)`);

val NEXT_CORE_STM_TN_W1 = store_thm("NEXT_CORE_STM_TN_W1",
   `!w y reg ireg alub alua.
      (w = LENGTH (REGISTER_LIST (w2n ireg))) ==>
      1 < w ==>
      (!t. t < SUC w ==> FST (i t)) ==>
      ?ointstart' obaselatch' onfq' ooonfq' oniq' oooniq' pipeaabt' pipebabt' dataabt2' aregn' oareg' mul' mul2' borrow2' mshift'.
        ~(num2exception aregn' IN {reset; undefined; software; address}) /\ (aregn' < 8) /\
        ((num2exception aregn' = fast) ==> ~WORD_BIT 6 (CPSR_READ psr)) /\
        ((num2exception aregn' = interrupt) ==> ~WORD_BIT 7 (CPSR_READ psr)) /\
       (FUNPOW (SNEXT NEXT_ARM6) (w - 1) <|state := ARM6
                 (DP reg psr (base + w32 1 * w32 4) din alua alub dout)
                 (CTRL pipea T pipeb T ireg T ointstart F F obaselatch F stm tn
                   T F F onfq ooonfq oniq oooniq pipeaabt pipebabt pipebabt dataabt2
                   aregn2 T T T sctrlreg psrfb oareg (MASKN 16 2 (w2n ireg))
                   (RP stm (w2n (ireg)) (MASKN 16 1 (w2n ireg)))
                   (RP stm (w2n (ireg)) (ONECOMP 16 0)) mul mul2 borrow2 mshift); inp := ADVANCE 2 i|> =
       (let nbs = if WORD_BIT 22 ireg then usr else DECODE_MODE (WORD_BITS 4 0 (CPSR_READ psr)) in
        <|state := ARM6 (DP reg psr (REG_READ6 reg usr 15) pipeb alua alub
                 (REG_READ6 reg nbs (RP stm (w2n ireg) (MASKN 16 (w - 1) (w2n ireg)))))
              (CTRL pipea T pipea T pipeb T ointstart' T T obaselatch' T
                 (if ointstart' then swi_ex else DECODE_INST (w2n pipeb)) t3
                 F F F onfq' ooonfq' oniq' oooniq' pipeaabt' pipeaabt' pipebabt' dataabt2'
                 (if ointstart' then aregn' else 2) T T F sctrlreg (SPSR_READ psr nbs) oareg'
                 (MASK (if ointstart' then swi_ex else DECODE_INST (w2n pipeb)) t3 ARB ARB)
                 (RP stm (w2n ireg) (MASKN 16 w (w2n ireg)))
                 (RP stm (w2n ireg) (MASKN 16 (w - 1) (w2n ireg)))
                 mul' mul2' borrow2' mshift'); inp := ADVANCE (w + 1) i|>))`,
  REPEAT STRIP_TAC
    THEN `~(WORD_BITS 15 0 ireg = 0)` by ASM_SIMP_TAC arith_ss [PENCZ_THM2]
    THEN PAT_ASSUM `w = LENGTH (REGISTER_LIST (w2n ireg))` SUBST_ALL_TAC
    THEN IMP_RES_TAC NEXT_CORE_STM_TN_W2
    THEN POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL)
    THEN ASM_SIMP_TAC std_ss [FUNPOW_SUC,DECIDE ``!x. 1 < x ==> (x - 1 = SUC (x - 2))``]
    THEN POP_ASSUM (K ALL_TAC)
    THEN PURE_REWRITE_TAC [SNEXT_NEXT_ARM6,pairTheory.FST,pairTheory.SND]
    THEN ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [NEXT_CORE_STM_TN1,MASK_def,PENCZ_THM,SUC_SUC_SUB2,
           GSYM io_onestepTheory.ADVANCE_COMP,DECIDE ``!x. 1 < x ==> (1 + (x - 2) + 2 = x + 1)``]
    THEN ABBREV_TAC `nbs = if WORD_BIT 22 ireg then usr else DECODE_MODE (WORD_BITS 4 0 (CPSR_READ psr))`
    THEN POP_ASSUM (K ALL_TAC)
    THEN RW_TAC arith_ss [MASK_def,PENCZ_THM,SUC_SUC_SUB2,io_onestepTheory.ADVANCE_def,
                          AREGN1_def,pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY]
    THEN FULL_SIMP_TAC arith_ss [num2exception_thm,exception_distinct,BIT_W32_NUM]
    THEN METIS_TAC [SIMP_RULE (std_ss++pred_setSimps.PRED_SET_ss) [] interrupt_exists]
);

val NEXT_CORE_STM_TN_W1 = save_thm("NEXT_CORE_STM_TN_W1",
  (GEN_ALL o SIMP_RULE bool_ss [] o
   DISCH `Abbrev (nbs = DECODE_MODE (WORD_BITS 4 0 cpsr))` o
   DISCH `Abbrev (cpsr = CPSR_READ psr)` o SPEC_ALL o
   SIMP_RULE std_ss [WORD_ADD_0,WORD_MULT_CLAUSES]) NEXT_CORE_STM_TN_W1
);

(* -------------------------------------------------------- *)

val DECODE_INST_LDM = prove(
  `!i. (DECODE_INST i = ldm) ==> BIT 20 i`,
  RW_TAC arith_ss [DECODE_INST_def]
);

val DECODE_INST_STM = prove(
  `!i. (DECODE_INST i = stm) ==> ~BIT 20 i`,
  RW_TAC arith_ss [DECODE_INST_def]
);

val DECODE_INST_LDM = save_thm("DECODE_INST_LDM",
  (GEN_ALL o REWRITE_RULE [BIT_W32_NUM] o SPEC `w2n ireg`) DECODE_INST_LDM);
val DECODE_INST_STM = save_thm("DECODE_INST_STM",
  (GEN_ALL o REWRITE_RULE [BIT_W32_NUM] o SPEC `w2n ireg`) DECODE_INST_STM);

val WORD_BITS_150_ZERO = store_thm("WORD_BITS_150_ZERO",
  `!i. (WORD_BITS 15 0 i = 0) ==> ~WORD_BIT 15 i`,
  STRIP_TAC THEN STRUCT_CASES_TAC (SPEC `i` word_nchotomy)
    THEN RW_TAC arith_ss [WORD_BIT_def,WORD_BITS_def,w2n_EVAL,MOD_WL_THM,BITS_ZERO2,
                          BITS_COMP_THM2,HB_def,BIT_def]
    THEN REWRITE_TAC [GSYM BIT_def]
    THEN RULE_ASSUM_TAC (CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [(SYM o SPECL [`15`,`0`]) BITS_ZERO2])))
    THEN FULL_SIMP_TAC arith_ss [BIT_ZERO,GSYM BIT_BITS_THM]
);

(* -------------------------------------------------------- *)
(* -------------------------------------------------------- *)

val _ = export_theory();
