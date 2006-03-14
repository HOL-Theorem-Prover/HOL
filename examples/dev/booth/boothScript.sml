(* app load ["bitsLib","bitsTheory","word32Theory"]; *)
open bitsLib simpLib HolKernel boolLib bossLib Parse Q arithmeticTheory whileTheory bitsTheory word32Theory;

val _ = type_abbrev("word", ``:word32``);

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

(* -------------------------------------------------------- *)
(* WL must be even *)

val WL_EVEN = prove(
  `WL MOD 2 = 0`,
  SIMP_TAC arith_ss [WL_def,HB_def]
);

(* -------------------------------------------------------- *)

val _ = new_theory "booth";

(* -------------------------------------------------------- *)

val _ = Hol_datatype `state_BOOTH = BOOTH of num=>num=>bool=>num=>word=>word`;
(* mul,mul2,borrow2,mshift,rm,rd *)

(* -------------------------------------------------------- *)

val MOD_CNTW_def = Define `MOD_CNTW n = n MOD (WL DIV 2)`;

(* -------------------------------------------------------- *)



val MSHIFT_def = Define`
  MSHIFT borrow mul count1 =
    count1 * 2 +
    if borrow /\ (mul = 1) \/ ~borrow /\ (mul = 2) then 1 else 0`;

val ALU_def = Define`
  ALU borrow2 mul alua alub =
    if ~borrow2 /\ (mul = 0) \/ borrow2 /\ (mul = 3) then
      alua
    else if borrow2 /\ (mul = 0) \/ (mul = 1) then
      alua + alub
    else
      alua - alub`;

val INIT_def = Define`
  INIT a rm rs rn =
    let mul1 = w2n rs
    and alub = rn
    and borrow = F
    and count1 = 0 in
    let rd = if a then alub else 0w
    and borrow2 = borrow
    and mul = BITS 1 0 mul1
    and mul2 = BITS HB 2 mul1 in
    let mshift = if mul = 2 then 1 else 0 in
     BOOTH mul mul2 borrow2 mshift rm rd`;

val INIT = save_thm("INIT",SIMP_RULE std_ss [GSYM WORD_BITS_def] INIT_def);

val NEXT_def = Define`
  NEXT (BOOTH mul mul2 borrow2 mshift rm rd) =
    let mul1 = BITS (HB - 2) 0 mul2
    and alub = rm << mshift
    and alua = rd
    and borrow = BIT 1 mul
    and count1 = MOD_CNTW (mshift DIV 2 + 1) in
    let rd' = ALU borrow2 mul alua alub
    and borrow2' = borrow
    and mul' = BITS 1 0 mul1
    and mul2' = BITS HB 2 mul1 in
    let mshift' = MSHIFT borrow mul' count1
    in
      BOOTH mul' mul2' borrow2' mshift' rm rd'`;

val NEXT = save_thm("NEXT",SIMP_RULE std_ss [] NEXT_def);

val STATE_def = Define`
  (STATE 0 a rm rs rn = INIT a rm rs rn) /\
  (STATE (SUC t) a rm rs rn = NEXT (STATE t a rm rs rn))`;

(* -------------------------------------------------------- *)

val BORROW2_def = Define`
  BORROW2 rs n = ~(n = 0) /\ WORD_BIT (2 * n - 1) rs`;

(*
val DONE_def = Define`
  DONE rs n = (WORD_BITS HB (2 * n) rs = 0) /\ ~BORROW2 rs n \/ ~(2 * n < WL)`;

With the ARM6, 1 cycle is taken in the rs = word_0 case.  This is used for CPSR update.
*)

val DONE_def = Define`
  DONE rs n = ~(n = 0) /\ (WORD_BITS HB (2 * n) rs = 0) /\ ~BORROW2 rs n \/ ~(2 * n < WL)`;

val DUR_def = Define`DUR rs = LEAST n. DONE rs n`;

val PROJ_RD_def = Define`
  PROJ_RD (BOOTH mul mul2 borrow2 mshift rm rd) = rd`;

val BOOTHMULTIPLY_def = Define`
  BOOTHMULTIPLY a rm rs rn = PROJ_RD (STATE (DUR rs) a rm rs rn)`;

(* -------------------------------------------------------- *)

(*
    and mulz = (BITS (HB - 2) 0 mul2 = 0 in
    let mulx = (mulz /\ ~borrow) \/ (BITS CNTW 1 mshift = 15) in
*)

val INVARIANT_def = Define`
  INVARIANT a rm rs rn n =
    let mul  = BITS 1 0 (WORD_BITS HB (2 * n) rs)
    and mul2 = WORD_BITS HB (2 * (n + 1)) rs
    and borrow2 = BORROW2 rs n in
      BOOTH mul mul2 borrow2
            (2 * (MOD_CNTW n) + if borrow2 /\ (mul = 1) \/
                                  ~borrow2 /\ (mul = 2) then 1 else 0)
            rm ((if borrow2 then
                   rm * n2w (w2n rs MOD 2 ** (2 * n)) - rm << (2 * n)
                 else
                   rm * n2w (w2n rs MOD 2 ** (2 * n))) + (if a then rn else 0w))`;

val INVARIANT = save_thm("INVARIANT",SIMP_RULE std_ss [] INVARIANT_def);

(* -------------------------------------------------------- *)

val MIN_HB_1 = prove(
  `MIN HB 1 = 1`,
  SIMP_TAC arith_ss [MIN_DEF,HB_def]
);

val MOD_4_BITS = prove(
  `!a. a MOD 4 = BITS 1 0 a`,
  SIMP_TAC arith_ss [BITS_ZERO3]
);

val w2n_DIV_THM = prove(
  `!n rs. w2n rs DIV 2 ** n = WORD_BITS HB n rs`,
  REPEAT STRIP_TAC
    THEN STRUCT_CASES_TAC (SPEC `rs` word_nchotomy)
    THEN SIMP_TAC arith_ss [BITS_COMP_THM2,MIN_DEF,WORD_BITS_def,w2n_EVAL,MOD_WL_THM,BITS_DIV_THM]
);

val w2n_DIV_4 = (numLib.REDUCE_RULE o SPEC `2`) w2n_DIV_THM;

val MIN_LEM = prove(
  `(!x t. MIN x (x - 2 + 2 * (t + 1)) = x) /\
   (!x t. MIN x (x + 2 * (t + 1)) = x)`,
  RW_TAC arith_ss [MIN_DEF]
);

val TWO_T_PLUS_TWO = DECIDE ``!t. 2 * (t + 1) + 2 = 2 * (t + 2)``;

val BORROW2 = prove(
  `!n rs. BORROW2 rs n = ~(n = 0) /\ BIT 1 (w2n rs DIV 2 ** (2 * (n - 1)))`,
  Cases THEN SIMP_TAC arith_ss [BORROW2_def]
    THEN SIMP_TAC arith_ss [WORD_BIT_def,ADD1,BIT_def,BITS_THM,DIV_DIV_DIV_MULT,
                            ZERO_LT_TWOEXP,LEFT_ADD_DISTRIB]
    THEN SIMP_TAC (bool_ss++numSimps.ARITH_AC_ss) [GSYM EXP,ADD1]
);

(* -------------------------------------------------------- *)

val COMM_MULT_DIV = ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV;
val COMM_DIV_MULT = ONCE_REWRITE_RULE [MULT_COMM] DIV_MULT;

val MSHIFT_THM = prove(
  `!t. 2 * (t + 1) <= HB + 1 ==> (MOD_CNTW t = t)`,
  RW_TAC arith_ss [MOD_CNTW_def,WL_def,ADD1]
    THEN IMP_RES_TAC ((SIMP_RULE arith_ss [] o SPEC `2`) DIV_LE_MONOTONE)
    THEN FULL_SIMP_TAC arith_ss [COMM_MULT_DIV,LESS_MOD]
);

val WL_GE_2 = prove(
  `2 <= HB + 1`,
  SIMP_TAC arith_ss [WL_def,HB_def]
);

val MSHIFT_0 = (SIMP_RULE arith_ss [WL_GE_2] o SPEC `0`) MSHIFT_THM;

val state_BOOTH_11 = theorem("state_BOOTH_11");

(* -------------------------------------------------------- *)

val BIT_1_BITS = prove(
  `!t x rs. 2 * (t + 1) <= x + 1 ==>
            (BIT 1 (WORD_BITS x (2 * t) rs) =
             BIT 1 (WORD_BITS (2 * t + 1) (2 * t) rs))`,
  RW_TAC arith_ss [BIT_def,WORD_BITS_COMP_THM2,MIN_DEF]
);

val TIME_LT_WL_MIN = prove(
  `!t x. 2 * (t + 1) <= x + 1 ==> (MIN x (2 * t + 1) = 2 * t + 1)`,
  RW_TAC arith_ss [MIN_DEF]
);

val BIT_CONST = prove(
  `~(BIT 1 0) /\ ~(BIT 1 1) /\ (BIT 1 2) /\ (BIT 1 3)`,
  EVAL_TAC
);

val DIV_2_BITS = (GEN_ALL o SYM o numLib.REDUCE_RULE o INST [`n` |-> `1`] o SPEC_ALL) WORD_BITS_DIV_THM;

val BIT_VAR = prove(
  `!t x. ~(WORD_BITS (t + 1) t x = 0) /\ ~(WORD_BITS (t + 1) t x = 1) ==>
          BIT 1 (WORD_BITS (t + 1) t x)`,
  RW_TAC arith_ss [BIT_def,WORD_BITS_COMP_THM2,MIN_DEF,DIV_2_BITS]
    THEN Cases_on `WORD_BITS (t + 1) t x = 2`
    THEN1 ASM_SIMP_TAC arith_ss []
    THEN Cases_on `WORD_BITS (t + 1) t x = 3`
    THEN1 ASM_SIMP_TAC arith_ss []
    THEN ASSUME_TAC ((SIMP_RULE arith_ss [ADD1] o SPECL [`t + 1`,`t`,`x`]) WORD_BITSLT_THM)
    THEN DECIDE_TAC
);

val MUST_BE_TWO = prove(
  `!t x. ~(WORD_BITS (t + 1) t x = 0) /\
         ~(WORD_BITS (t + 1) t x = 1) /\
         ~(WORD_BITS (t + 1) t x = 3) ==>
          (WORD_BITS (t + 1) t x = 2)`,
  REPEAT STRIP_TAC
    THEN Cases_on `WORD_BITS (t + 1) t x = 2`
    THEN1 ASM_REWRITE_TAC []
    THEN ASSUME_TAC ((SIMP_RULE arith_ss [ADD1] o SPECL [`t + 1`,`t`,`x`]) WORD_BITSLT_THM)
    THEN DECIDE_TAC
);

val MUST_BE_THREE = prove(
  `!t x. ~(WORD_BITS (t + 1) t x = 0) /\
         ~(WORD_BITS (t + 1) t x = 1) /\
         ~(WORD_BITS (t + 1) t x = 2) ==>
          (WORD_BITS (t + 1) t x = 3)`,
  REPEAT STRIP_TAC
    THEN Cases_on `WORD_BITS (t + 1) t x = 3`
    THEN1 ASM_REWRITE_TAC []
    THEN ASSUME_TAC ((SIMP_RULE arith_ss [ADD1] o SPECL [`t + 1`,`t`,`x`]) WORD_BITSLT_THM)
    THEN DECIDE_TAC
);

(* -------------------------------------------------------- *)

val ssd = simpLib.SSFRAG {ac = [(SPEC_ALL WORD_ADD_ASSOC, SPEC_ALL WORD_ADD_COMM),
                                 (SPEC_ALL WORD_MULT_ASSOC, SPEC_ALL WORD_MULT_COMM)],
                congs = [], convs = [], dprocs = [], filter = NONE, rewrs = []};
val word_ss = bool_ss++ssd;

val SPEC_SLICE_COMP = prove(
  `!t a. ~(t = 0) ==>
         (a MOD 2 ** (2 * (t + 1)) =
          SLICE (2 * t + 1) (2 * t) a + a MOD 2 ** (2 * t))`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC NOT_ZERO_ADD1
    THEN ASM_SIMP_TAC arith_ss [DECIDE (Term `!p. 2 * SUC p = SUC (2 * p + 1)`),
                               GSYM BITS_ZERO3,GSYM SLICE_ZERO_THM,SLICE_COMP_RWT]
    THEN SIMP_TAC arith_ss [SLICE_ZERO_THM,BITS_ZERO3,ADD1,LEFT_ADD_DISTRIB]
);

val MULT_MOD_SUC_T = prove(
  `!t a b.  a * n2w (w2n b MOD 2 ** (2 * (t + 1))) =
            (a * n2w (w2n b MOD 2 ** (2 * t))) + (a * n2w (WORD_SLICE (2 * t + 1) (2 * t) b))`,
  REPEAT STRIP_TAC
    THEN Cases_on `t = 0`
    THEN1 ASM_SIMP_TAC arith_ss [WORD_MULT_CLAUSES,WORD_ADD_CLAUSES,
                                 MOD_4_BITS,GSYM WORD_BITS_def,WORD_SLICE_ZERO_THM]
    THEN ASM_SIMP_TAC bool_ss [SPEC_SLICE_COMP,GSYM WORD_SLICE_def,GSYM ADD_EVAL,
                               WORD_LEFT_ADD_DISTRIB,WORD_ADD_COMM]
);

val MULT_LEM = prove(
  `!a b c. a * n2w (b * c) = (a * n2w c) * n2w b`,
  SIMP_TAC word_ss [GSYM MUL_EVAL]
);

val MULT_MOD_SUC_T = REWRITE_RULE [MULT_LEM,WORD_SLICE_THM,GSYM word_lsl] MULT_MOD_SUC_T;

val WORD_DOUBLE = prove(
  `!a. a + a = a * 2w`,
  STRIP_TAC THEN STRUCT_CASES_TAC (SPEC `a` word_nchotomy)
    THEN SIMP_TAC arith_ss [(* MULT_COMM,*)ADD_EVAL,MUL_EVAL]
);

val MULT_FOUR = prove(
  `!a. a * 4w = (a * 2w) + (a * 2w)`,
  STRIP_TAC THEN STRUCT_CASES_TAC (SPEC `a` word_nchotomy)
    THEN SIMP_TAC arith_ss [ADD_EVAL,MUL_EVAL]
);

val MULT_TWO_LSL = prove(
  `!rm t. (rm << (2 * t)) * 2w = rm << (2 * t + 1)`,
  SIMP_TAC arith_ss [word_lsl,GSYM WORD_MULT_ASSOC,MUL_EVAL,GSYM ADD1,EXP]);

 (*,MULT_COMM]*)

val MULT_FOUR_LSL = prove(
  `!t rm. rm << (2 * (t + 1)) = (rm << (2 * t)) * 4w`,
  SIMP_TAC arith_ss [word_lsl,GSYM WORD_MULT_ASSOC,MUL_EVAL,LEFT_ADD_DISTRIB,EXP_ADD]
);

val lem2 = prove(
  `!a. a * 4w = (a * 3w) + a`,
  STRIP_TAC THEN STRUCT_CASES_TAC (SPEC `a` word_nchotomy)
    THEN REWRITE_TAC [MUL_EVAL,ADD_EVAL,DECIDE (Term `a * 4 = a * 3 + a`)]
);

val lem3 = prove(
  `!a b. (a + (b * 3w)) - (b * 4w) = a - b`,
  REWRITE_TAC [lem2,WORD_ADD_SUB_ASSOC,WORD_ADD_SUB3,GSYM word_sub]
);

val MULT_THREE_LSL = prove(
  `!t x rm. x + rm << (2 * t) * 3w - rm << (2 * (t + 1)) =
            x - rm << (2 * t)`,
  REWRITE_TAC [MULT_FOUR_LSL,lem3]
);

val MULT_TWO_LSL2a = prove(
  `!t x rm.  x + rm << (2 * t + 1) - rm << (2 * (t + 1)) =
             x - rm << (2 * t + 1)`,
  REWRITE_TAC [GSYM MULT_TWO_LSL,MULT_FOUR_LSL]
    THEN REWRITE_TAC [MULT_FOUR,WORD_SUB_PLUS,WORD_ADD_SUB]
);

val MULT_TWO_LSL2b = prove(
  `!t x rm. x - rm << (2 * t) - rm << (2 * t) =
            x - rm << (2 * t + 1)`,
  REWRITE_TAC [GSYM WORD_SUB_PLUS,WORD_DOUBLE,GSYM MULT_TWO_LSL]
);

val MULT_ONE_LSL = prove(
  `!t x rm.  x + rm << (2 * t + 1) - rm << (2 * t) =
             x + rm << (2 * t)`,
  REWRITE_TAC [WORD_ADD_ASSOC,GSYM MULT_TWO_LSL,GSYM WORD_DOUBLE,WORD_ADD_SUB]
);

val MULT_TWO_LSL2a_0 = (numLib.REDUCE_RULE o SPEC `0`) MULT_TWO_LSL2a;
val MULT_TWO_LSL2b_0 = (REWRITE_RULE [WORD_ADD_CLAUSES] o SPEC `0w`) MULT_TWO_LSL2a_0;

val LSL_CONST = prove(
  `(!a. a * 2w = a << 1) /\
   (!a. a * 4w = a << 2)`,
  SIMP_TAC arith_ss [word_lsl]
);

val MULT_THREE_LSL_0 = (SIMP_RULE arith_ss [WORD_ADD_0,ZERO_SHIFT2] o SPEC `0`) MULT_THREE_LSL;
val MULT_THREE_LSL_0b = (REWRITE_RULE [WORD_ADD_CLAUSES] o SPEC `0w`) MULT_THREE_LSL_0;

val WORD_ADD_COMM_ASSOC = prove(
  `!c a b. (a + b) + c = (a + c) + b`,
  SIMP_TAC word_ss []
);

val MOVE_RM = (GEN_ALL o SPEC `x << n` o GSYM) WORD_ADD_COMM_ASSOC;
val MOVE_RM2 = (GEN_ALL o INST [`b` |-> `x * 3w`] o SPEC_ALL) WORD_ADD_COMM_ASSOC;

(* -------------------------------------------------------- *)

val INVARIANT_CORRECT = store_thm("INVARIANT_CORRECT",
  `!t a rm rs rn. 2 * t <= WL ==> (STATE t a rm rs rn = INVARIANT a rm rs rn t)`,
  REWRITE_TAC [WL_def]
    THEN Induct
    THEN1 SIMP_TAC arith_ss [WORD_BITS_COMP_THM2,MIN_HB_1,WORD_MULT_CLAUSES,
            WORD_ADD_CLAUSES,MSHIFT_0,BITS_ZERO2,STATE_def,COND_RAND,INIT,INVARIANT,BORROW2_def]
    THEN ASM_SIMP_TAC arith_ss [STATE_def, INVARIANT, NEXT, WORD_BITS_COMP_THM2, MSHIFT_THM,
           BORROW2, ADD1, TIME_LT_WL_MIN, w2n_DIV_THM,
           TWO_T_PLUS_TWO, MSHIFT_def, BIT_1_BITS, MIN_LEM, state_BOOTH_11]
    THEN REPEAT STRIP_TAC
    THEN1 RW_TAC arith_ss [COMM_MULT_DIV,COMM_DIV_MULT]
    THEN RW_TAC arith_ss [ALU_def,WORD_EQ_ADD_RCANCEL]
    THEN FULL_SIMP_TAC arith_ss [BIT_CONST,MOD_4_BITS,GSYM WORD_BITS_def]
    THEN IMP_RES_TAC BIT_VAR
    THEN FULL_SIMP_TAC bool_ss [MULT_MOD_SUC_T,MOVE_RM,MOVE_RM2,
           WORD_MULT_CLAUSES,WORD_ADD_CLAUSES,ZERO_SHIFT2,
           MUST_BE_TWO,MUST_BE_THREE,GSYM WORD_ADD_SUB_SYM,WORD_ADD_SUB,
           MULT_ONE_LSL,MULT_TWO_LSL,MULT_TWO_LSL2a,MULT_TWO_LSL2b,MULT_THREE_LSL]
    THEN TRY (PAT_ASSUM `t = 0` (fn th => RULE_ASSUM_TAC (SIMP_RULE arith_ss [th])))
    THEN ASM_SIMP_TAC word_ss [LSL_CONST,WORD_MULT_CLAUSES,MULT_TWO_LSL2a_0,
           MULT_TWO_LSL2b_0,MULT_THREE_LSL_0,MULT_THREE_LSL_0b,
           (numLib.REDUCE_RULE o SPEC `0`) MUST_BE_THREE]
);

(* -------------------------------------------------------- *)

val EXISTS_DONE = prove(
  `!rs. ?n. DONE rs n`,
  RW_TAC bool_ss [DONE_def]
    THEN EXISTS_TAC `WL DIV 2`
    THEN SIMP_TAC arith_ss [DIV_MULT_THM2,WL_EVEN]
);

val lem = (SIMP_RULE bool_ss [EXISTS_DONE] o SPECL [`\x. 2 * x <= WL`,`DONE rs`]) LEAST_ELIM;

val SPEC_LESS_MULT_MONO = (GEN_ALL o numLib.REDUCE_RULE o INST [`n` |-> `1`] o SPEC_ALL) LESS_MULT_MONO;

val DIV_TWO_MONO_EVEN = prove(
  `!a b. a < 2 * b = a DIV 2 < b`,
  REPEAT STRIP_TAC
    THEN Cases_on `EVEN a`
    THENL [
      IMP_RES_TAC EVEN_EXISTS
        THEN ASM_SIMP_TAC arith_ss [COMM_MULT_DIV,SPEC_LESS_MULT_MONO],
      RULE_ASSUM_TAC (REWRITE_RULE [GSYM ODD_EVEN])
        THEN IMP_RES_TAC ODD_EXISTS
        THEN ASM_SIMP_TAC arith_ss [ADD1,COMM_DIV_MULT,SPEC_LESS_MULT_MONO]
    ]
);

val WL_DIV_MULT_TWO_ID = (SYM o ONCE_REWRITE_RULE [MULT_COMM] o SIMP_RULE arith_ss [WL_EVEN] o
                          CONJUNCT1 o SPEC `WL` o numLib.REDUCE_RULE o SPEC `2`) DIVISION;

val DONE_LESS_EQUAL_WL = prove(
    `!n. (!m. m < n ==> ~DONE rs m) /\ DONE rs n ==> 2 * n <= WL`,
    RW_TAC bool_ss [DONE_def,NOT_LESS]
    THENL [
      FULL_SIMP_TAC arith_ss [BORROW2_def]
         THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
         THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS_EQUAL])
         THEN IMP_RES_TAC DIV_TWO_MONO_EVEN
         THEN PAT_ASSUM `!m. m < n ==> P` IMP_RES_TAC
         THEN `2 * (WL DIV 2) = (WL DIV 2) * 2` by PROVE_TAC [MULT_COMM]
              THEN FULL_SIMP_TAC arith_ss [WL_DIV_MULT_TWO_ID]
      ,
      Cases_on `2 * n = WL` THEN1 ASM_SIMP_TAC arith_ss []
         THEN `WL < 2 * n` by DECIDE_TAC
         THEN IMP_RES_TAC DIV_TWO_MONO_EVEN
         THEN PAT_ASSUM `!m. m < n ==> P` IMP_RES_TAC
         THEN `2 * (WL DIV 2) = WL DIV 2 * 2` by PROVE_TAC [MULT_COMM]
         THEN FULL_SIMP_TAC arith_ss [WL_DIV_MULT_TWO_ID]
     ]);




val DUR_LT_EQ_HWL = prove(
  `!rs. 2 * (DUR rs) <= WL`,
  REWRITE_TAC [DUR_def]
    THEN CONV_TAC (DEPTH_CONV ETA_CONV)
    THEN PROVE_TAC [DONE_LESS_EQUAL_WL,lem]
);

(* -------------------------------------------------------- *)

val lem = (SIMP_RULE bool_ss [EXISTS_DONE] o
           SPECL [`\x. 2 * x < WL ==> ~(BORROW2 rs x)`,`DONE rs`]) LEAST_ELIM;

val DONE_EARLY_NOT_BORROW = prove(
  `!n. (!m. m < n ==> ~DONE rs m) /\ DONE rs n ==>
          2 * n < WL ==>
          ~BORROW2 rs n`,
  RW_TAC arith_ss [DONE_def,BORROW2_def]
    THEN FULL_SIMP_TAC bool_ss []
);

val DONE_EARLY_NOT_BORROW2 = prove(
  `!rs. 2 * (DUR rs) < WL ==> ~BORROW2 rs (DUR rs)`,
  REWRITE_TAC [DUR_def]
    THEN CONV_TAC (DEPTH_CONV ETA_CONV)
    THEN PROVE_TAC [MATCH_MP lem DONE_EARLY_NOT_BORROW]
);

val BORROW_IMP_WL = prove(
  `!rs. BORROW2 rs (DUR rs) ==> (2 * (DUR rs) = WL)`,
  REPEAT STRIP_TAC
    THEN Cases_on `2 * (DUR rs) < WL`
    THEN1 IMP_RES_TAC DONE_EARLY_NOT_BORROW2
    THEN ASSUME_TAC (SPEC `rs` DUR_LT_EQ_HWL)
    THEN DECIDE_TAC
);

val lem = (SIMP_RULE bool_ss [EXISTS_DONE] o
           SPECL [`\x. w2n rs MOD 2 ** (2 * x) = w2n rs`,`DONE rs`]) LEAST_ELIM;

val ZERO_LT_WL = simpLib.SIMP_PROVE arith_ss [WL_def] ``0 < WL``;

val DONE_IMP_ZERO_MSBS = prove(
  `!n. (!m. m < n ==> ~DONE rs m) /\ DONE rs n ==>
        (w2n rs MOD 2 ** (2 * n) = w2n rs)`,
   STRUCT_CASES_TAC (SPEC `rs` word_nchotomy)
     THEN RW_TAC arith_ss [WL_def,SUC_SUB1,w2n_EVAL,DONE_def,MOD_WL_THM,WORD_BITS_def,BITS_COMP_THM2]
     THENL [
       Cases_on `n'` THEN1 FULL_SIMP_TAC arith_ss [ZERO_MOD]
         THEN FULL_SIMP_TAC bool_ss [GSYM BITS_ZERO3,DECIDE ``!n. 2 * SUC n = SUC (2 * n + 1)``]
         THEN RW_TAC arith_ss [BITS_COMP_THM2,MIN_DEF]
         THEN Cases_on `2 * n'' + 1 = HB` THEN1 ASM_REWRITE_TAC []
         THEN `2 * n'' + 2 <= HB` by FULL_SIMP_TAC arith_ss [NOT_LESS]
         THEN `SLICE HB (SUC (2 * n'' + 1)) n = 0` by ASM_SIMP_TAC arith_ss [SLICE_THM]
         THEN IMP_RES_TAC ((GSYM o SIMP_RULE arith_ss [ADD1,SLICE_ZERO_THM] o
                                      SPECL [`HB`,`2 * n'' + 1`,`0`]) SLICE_COMP_THM)
         THEN POP_ASSUM (ASSUME_TAC o SPEC `n`)
         THEN FULL_SIMP_TAC arith_ss [ADD1],
       FULL_SIMP_TAC bool_ss [NOT_LESS]
         THEN IMP_RES_TAC LESS_EQUAL_ADD
         THEN STRIP_ASSUME_TAC (REWRITE_RULE [ADD,WL_def] (MATCH_MP LESS_ADD_1 ZERO_LT_WL))
         THEN ASM_SIMP_TAC bool_ss [ADD_SUB,DECIDE ``!a b. a + 1 + b = SUC (a + b)``,GSYM BITS_ZERO3]
         THEN RW_TAC arith_ss [BITS_COMP_THM2,MIN_DEF]
         THEN `p = 0` by DECIDE_TAC
         THEN FULL_SIMP_TAC arith_ss [ADD1]
     ]
);

val DUR_IMP_ZERO_MSBS = prove(
  `!rs. w2n rs MOD 2 ** (2 * (DUR rs)) = w2n rs`,
  REWRITE_TAC [DUR_def]
    THEN CONV_TAC (DEPTH_CONV ETA_CONV)
    THEN PROVE_TAC [MATCH_MP lem DONE_IMP_ZERO_MSBS]
);

val SPEC_LSL_LIMIT = (GEN_ALL o REWRITE_RULE [GSYM WL_def] o
                      SIMP_RULE arith_ss [WL_def] o SPECL [`a`,`WL`]) LSL_LIMIT;

(* -------------------------------------------------------- *)

val CORRECT = store_thm("CORRECT",
  `!a rm rs rn. BOOTHMULTIPLY a rm rs rn =
                rm * rs + (if a then rn else 0w)`,
  SIMP_TAC bool_ss [DUR_LT_EQ_HWL,BOOTHMULTIPLY_def,INVARIANT_CORRECT,INVARIANT,PROJ_RD_def,BORROW_IMP_WL,
                    DUR_IMP_ZERO_MSBS,w2n_ELIM,SPEC_LSL_LIMIT,WORD_SUB_RZERO]
);

(* -------------------------------------------------------- *)

val if_swp = PROVE [] ``!a b c. (if ~a then b else c) = (if a then c else b)``;

val SPEC_BIT_BITS_THM =
  (GEN_ALL o SYM o REWRITE_RULE [BITS_ZERO2,BIT_ZERO] o INST [`b` |-> `0`] o SPEC_ALL) BIT_BITS_THM;

val EXTEND_ONE_BIT = prove(
  `!h l n. l < h /\ (l2 = SUC l) ==> (~(BITS h l2 n = 0) \/ BIT l n = ~(BITS h l n = 0))`,
  RW_TAC bool_ss [GSYM LESS_EQ,SPEC_BIT_BITS_THM]
    THEN EQ_TAC THEN RW_TAC arith_ss []
    THENL [
      EXISTS_TAC `x` THEN ASM_SIMP_TAC arith_ss [],
      EXISTS_TAC `l` THEN ASM_SIMP_TAC arith_ss [],
      Cases_on `l = x` THEN1 ASM_REWRITE_TAC []
        THEN DISJ1_TAC THEN EXISTS_TAC `x` THEN ASM_SIMP_TAC arith_ss []
    ]
);

val DUR_EVAL = save_thm("DUR_EVAL",
  (GEN_ALL o SIMP_RULE std_ss [if_swp,EXTEND_ONE_BIT] o
   SIMP_RULE arith_ss [HB_def,GSYM BIT_def,WL_def])
    (funpow 17 (ONCE_REWRITE_RULE [WHILE])
       ((SIMP_RULE arith_ss [LEAST_DEF,DONE_def,BORROW2_def,BIT_def,MIN_DEF,
                             BITS_EVAL,BIT_EVAL,MOD_WL_THM,BITS_COMP_THM2] o SPEC `n2w n`) DUR_def))
);

(* -------------------------------------------------------- *)


val _ = export_theory();
