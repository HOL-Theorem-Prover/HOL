(* ========================================================================= *)
(* FILE          : lemmasScript.sml                                          *)
(* DESCRIPTION   : A collection of lemmas used to verify correctness         *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2001 - 2005                                               *)
(* ========================================================================= *)

(* interactive use:
  app load ["wordsLib", "armTheory", "coreTheory", "armLib"];
*)

open HolKernel boolLib bossLib;
open Q numLib combinTheory arithmeticTheory;
open bitTheory wordsLib wordsTheory armTheory coreTheory;

val _ = new_theory "lemmas";

(* ------------------------------------------------------------------------- *)

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

val fcp_ss   = armLib.fcp_ss;
val SIZES_ss = wordsLib.SIZES_ss;

val tt = set_trace "types";

(* ------------------------------------------------------------------------- *)

val arm6inp_nchotomy = save_thm("arm6inp_nchotomy",
  armLib.tupleCases
  ``(NRESET:bool, ABORT:bool, NFQ:bool, NIQ:bool,
     DATA:word32, CPA:bool, CPB:bool)``);

val arm6_nchotomy = save_thm("arm6_nchotomy",
  armLib.combCases ``ARM6 (DP reg psr areg din alua alub dout)
    (CTRL pipea pipeaval pipeb pipebval ireg iregval ointstart onewinst
        endinst obaselatch opipebll nxtic nxtis nopc1 oorst resetlatch onfq
        ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2 aregn2 mrq2
        nbw nrw sctrlreg psrfb oareg mask orp oorp mul mul2 borrow2 mshift)``);

fun Cases_on_arm6inp tm = FULL_STRUCT_CASES_TAC (SPEC tm arm6inp_nchotomy);

val form_7tuple = save_thm("form_7tuple",
  (GEN_ALL o simpLib.SIMP_PROVE std_ss [])
    ``(a:bool # bool # bool # bool # word32 # bool # bool) =
      (FST a,FST (SND a),FST (SND (SND a)),FST (SND (SND (SND a))),
       FST (SND (SND (SND (SND a)))),FST (SND (SND (SND (SND (SND a))))),
       SND (SND (SND (SND (SND (SND a))))))``);

val SNEXT_NEXT_ARM6 = save_thm("SNEXT_NEXT_ARM6",
  (ONCE_REWRITE_RULE [form_7tuple] o SIMP_RULE (srw_ss()) [] o
   SPEC `<|state := a; inp := i|>` o
   REWRITE_RULE [FUN_EQ_THM] o ISPEC `NEXT_ARM6`) io_onestepTheory.SNEXT_def);

val COND_PAIR = save_thm("COND_PAIR",
  (GEN_ALL o PROVE []) ``(if e then (a,b) else (c,d)) =
                         (if e then a else c,if e then b else d)``);

(* ------------------------------------------------------------------------- *)

val NOT_RESET_EXISTS = store_thm("NOT_RESET_EXISTS",
  `!t inp. ~IS_RESET inp t ==>
      ?ABORT NFQ NIQ DATA CPA CPB.
         (inp t = (T,IS_ABORT inp t,NFQ,NIQ,DATA,CPA,CPB))`,
  RW_TAC std_ss [IS_RESET_def,IS_ABORT_def]
    THEN Cases_on_arm6inp `inp (t:num)`
    THEN FULL_SIMP_TAC std_ss [PROJ_NRESET_def,PROJ_ABORT_def]);

val NOT_RESET_EXISTS2 = store_thm("NOT_RESET_EXISTS2",
  `!t inp. ~IS_RESET inp t ==>
      ?ABORT NFQ NIQ DATA CPA CPB. (inp t = (T,ABORT,NFQ,NIQ,DATA,CPA,CPB))`,
  RW_TAC std_ss [IS_RESET_def] \\ Cases_on_arm6inp `inp (t:num)`
    \\ FULL_SIMP_TAC std_ss [PROJ_NRESET_def]);

val MASK_MASK = store_thm("MASK_MASK",
  `!ic mask rp rp2.
     MASK ic t3 (MASK ic t3 mask rp) rp2 = MASK ic t3 mask rp`,
  RW_TAC std_ss [MASK_def]);

val SND_LSL = store_thm("SND_LSL",
  `!n a c. SND (LSL a n c) = a << w2n n`,
  RW_TAC arith_ss [LSL_def,SHIFT_ZERO,word_0_n2w]);

val LSL_ZERO = save_thm("LSL_ZERO",
  (REWRITE_RULE [SHIFT_ZERO,word_0_n2w] o SPEC `0w`) SND_LSL);

val LSL_TWO = save_thm("LSL_TWO",
  (SIMP_RULE (arith_ss++SIZES_ss) [w2n_n2w] o SPEC `2w`) SND_LSL);

val SND_ROR = store_thm("SND_ROR",
  `!a n c. SND (ROR a n c) = a #>> w2n n`,
  RW_TAC std_ss [ROR_def,LSL_def,SHIFT_ZERO,word_0_n2w]);

val IMMEDIATE_THM = store_thm("IMMEDIATE_THM",
  `!c i:word32.
     IMMEDIATE c ((11 >< 0) i) = ROR ((7 -- 0) i) (2w * (11 >< 8) i) c`,
  SIMP_TAC (arith_ss++SIZES_ss)
    [IMMEDIATE_def,MIN_DEF,word_extract_def,word_bits_w2w,w2w_id,w2w_w2w,
     WORD_BITS_COMP_THM]);

val IMMEDIATE_THM2 = store_thm("IMMEDIATE_THM2",
  `!c i. SND (IMMEDIATE c i) = SND (IMMEDIATE F i)`,
  RW_TAC std_ss [IMMEDIATE_def,ROR_def,LSL_def]);

val SHIFT_IMMEDIATE_THM2 = store_thm("SHIFT_IMMEDIATE_THM2",
  `!r m c i. SHIFT_IMMEDIATE r m c ((11 >< 0) i) =
    let rm = REG_READ r m ((3 >< 0) i) in
      SHIFT_IMMEDIATE2 ((11 >< 7) i) ((6 >< 5) i) rm c`,
  SIMP_TAC (arith_ss++SIZES_ss) [SHIFT_IMMEDIATE_def,MIN_DEF,WORD_BITS_COMP_THM,
    word_extract_def,word_bits_w2w,w2w_w2w]);

val SHIFT_REGISTER_THM2 = store_thm("SHIFT_REGISTER_THM2",
  `!r m c i. SHIFT_REGISTER r m c ((11 >< 0) i) =
    let shift = (7 >< 0) (REG_READ r m ((11 >< 8) i))
    and rm = REG_READ (INC_PC r) m ((3 >< 0) i) in
      SHIFT_REGISTER2 shift ((6 >< 5) i) rm c`,
  SIMP_TAC (arith_ss++SIZES_ss) [SHIFT_REGISTER_def,MIN_DEF,WORD_BITS_COMP_THM,
    word_extract_def,word_bits_w2w,w2w_w2w]);

val w2w_extract = store_thm("w2w_extract",
  `!w:bool ** 'a. w2w (((h >< l) w):bool ** 'b) =
     (MIN h (dimindex (:'b) - 1 + l) -- l) w`,
  SIMP_TAC arith_ss [word_extract_def,w2w_w2w,w2w_id,
    WORD_BITS_COMP_THM]);

val CONCAT_MSR = store_thm("CONCAT_MSR",
  `!b i. 8 <= i /\ i <= 27 /\ b \/ i <= 7 /\ b <=> i < 28 /\ b`,
  Cases \\ SIMP_TAC arith_ss []);

(* ------------------------------------------------------------------------- *)

val LESS_THM =
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV prim_recTheory.LESS_THM;

val TEST_OR_COMP_LEM = prove(
  `!n. (BITS 24 23 n = 2) <=> BIT 24 n /\ ~BIT 23 n`,
  STRIP_TAC \\ SPECL_THEN [`24`,`23`,`n`]
       (ASSUME_TAC o SIMP_RULE arith_ss []) BITSLT_THM
    \\ FULL_SIMP_TAC arith_ss [LESS_THM,
         simpLib.SIMP_PROVE arith_ss [BIT_def,BITS_COMP_THM2]
           ``(!n. BIT 24 n = BIT 1 (BITS 24 23 n)) /\
             (!n. BIT 23 n = BIT 0 (BITS 24 23 n))``] \\ EVAL_TAC);

val start_tac =
  SIMP_TAC (arith_ss++SIZES_ss) [TEST_OR_COMP_def,ARITHMETIC_def,
         WORD_BITS_COMP_THM,word_extract_def,word_bits_w2w]
    \\ Cases \\ SIMP_TAC (std_ss++SIZES_ss) [word_bits_n2w,w2w_def]
    \\ ASM_SIMP_TAC bool_ss [w2n_n2w,n2w_11,MOD_DIMINDEX];

val TEST_OR_COMP_THM = store_thm("TEST_OR_COMP_THM",
  `!i:word32. TEST_OR_COMP ((24 >< 21) i) <=> i %% 24 /\ ~(i %% 23)`,
  start_tac \\ SIMP_TAC (fcp_ss++SIZES_ss) [n2w_def,EVAL ``BITS 3 0 2``,
    BITS_COMP_THM2,TEST_OR_COMP_LEM]);

val ARITHMETIC_THM = store_thm("ARITHMETIC_THM",
  `!i:word32. ARITHMETIC ((24 >< 21) i) <=>
           (i %% 23 \/ i %% 22) /\ (~(i %% 24) \/ ~(i %% 23))`,
  start_tac \\ SIMP_TAC (fcp_ss++SIZES_ss) [n2w_def,BIT_def,BITS_COMP_THM2]);

val ARITHMETIC_THM2 = store_thm("ARITHMETIC_THM2",
  `!i:word32. ~(i %% 23) /\ ~(i %% 22) \/ i %% 24 /\ i %% 23 <=>
         ~ARITHMETIC ((24 >< 21) i)`, RW_TAC bool_ss [ARITHMETIC_THM]);

(* ------------------------------------------------------------------------- *)

val ADD4_ADD4 = store_thm("ADD4_ADD4",
  `(!a. a + 4w + 4w = a + 8w)`,
  SIMP_TAC arith_ss [GSYM WORD_ADD_ASSOC,word_add_n2w]);

val ONE_COMP_THREE_ADD = store_thm("ONE_COMP_THREE_ADD",
  `!a:word32. a - 8w + 4w = ~3w + a`,
  STRIP_TAC \\ `~3w + a = a + ~3w` by PROVE_TAC [WORD_ADD_COMM]
    \\ POP_ASSUM SUBST1_TAC \\ RW_TAC bool_ss [WORD_NOT]
    \\ EVAL_TAC \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC,WORD_EQ_ADD_LCANCEL]
    \\ EVAL_TAC);

val REGISTER_RANGES =
  (SIMP_RULE (std_ss++SIZES_ss) [] o Thm.INST_TYPE [alpha |-> ``:4``]) w2n_lt;

val mode_reg2num_15 = (GEN_ALL o
  SIMP_RULE (arith_ss++SIZES_ss) [w2n_n2w] o
  SPECL [`m`,`15w`]) mode_reg2num_def;

val mode_reg2num_lt = store_thm("mode_reg2num_lt",
  `!w m w. mode_reg2num m w < 31`,
  ASSUME_TAC REGISTER_RANGES
    \\ RW_TAC std_ss [mode_reg2num_def,USER_def,DECIDE ``n < 16 ==> n < 31``]
    \\ Cases_on `m`
    \\ FULL_SIMP_TAC arith_ss [mode_distinct,mode_case_def,
         DECIDE ``a < 16 /\ b < 16 ==> (a + b < 31)``,
         DECIDE ``a < 16 /\ ~(a = 15) ==> (a + 16 < 31)``]);

val not_reg_eq_lem = prove(`!v w. ~(v = w) ==> ~(w2n v = w2n w)`,
  REPEAT Cases \\ SIMP_TAC std_ss [w2n_n2w,n2w_11]);

val not_reg_eq = store_thm("not_reg_eq",
  `!v w m1 m2. ~(v = w) ==> ~(mode_reg2num m1 v = mode_reg2num m2 w)`,
  NTAC 4 STRIP_TAC
    \\ `w2n v < 16 /\ w2n w < 16` by REWRITE_TAC [REGISTER_RANGES]
    \\ Cases_on `m1` \\ Cases_on `m2`
    \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss)
         [USER_def,mode_reg2num_def,not_reg_eq_lem]
    \\ COND_CASES_TAC \\ ASM_SIMP_TAC arith_ss [not_reg_eq_lem]
    \\ COND_CASES_TAC \\ ASM_SIMP_TAC arith_ss [not_reg_eq_lem]);

val not_pc = (GEN_ALL o REWRITE_RULE [mode_reg2num_15] o
  SPECL [`v`,`15w`]) not_reg_eq;

val r15 = SYM (List.nth (CONJUNCTS num2register_thm, 15))
val READ_TO_READ6 = store_thm("READ_TO_READ6",
  `!r m n d. (REG_READ (REG_WRITE r usr 15w (d - 8w)) m n =
              REG_READ6 (REG_WRITE r usr 15w d) m n)`,
  RW_TAC (std_ss++SIZES_ss) [REG_READ_def,REG_READ6_def,FETCH_PC_def,
         REG_WRITE_def,UPDATE_def,WORD_SUB_ADD,mode_reg2num_15]
  \\ PROVE_TAC [r15,num2register_11,mode_reg2num_lt,not_pc,DECIDE ``15 < 31``]);

val TO_WRITE_READ6 = store_thm("TO_WRITE_READ6",
  `(!r. FETCH_PC r = REG_READ6 r usr 15w) /\
   (!r. INC_PC r = REG_WRITE r usr 15w (REG_READ6 r usr 15w + 4w)) /\
   (!r. SUB8_PC r = REG_WRITE r usr 15w (REG_READ6 r usr 15w - 8w)) /\
   (!r m d. REG_WRITE r m 15w d = REG_WRITE r usr 15w d) /\
   (!r m. REG_READ6 r m 15w = REG_READ6 r usr 15w)`,
  RW_TAC std_ss [INC_PC_def,REG_READ6_def,REG_WRITE_def,REG_READ_def,
    FETCH_PC_def,SUB8_PC_def,mode_reg2num_15]);

val REG_WRITE_WRITE = store_thm("REG_WRITE_WRITE",
  `!r m n d1 d2. REG_WRITE (REG_WRITE r m n d1) m n d2 = REG_WRITE r m n d2`,
  RW_TAC bool_ss [REG_WRITE_def,UPDATE_EQ]);

val REG_WRITE_WRITE_COMM = store_thm("REG_WRITE_WRITE_COMM",
  `!r m n1 n2 d1 d2.
     ~(n1 = n2) ==>
      (REG_WRITE (REG_WRITE r m n1 d1) m n2 d2 =
       REG_WRITE (REG_WRITE r m n2 d2) m n1 d1)`,
  RW_TAC std_ss [REG_WRITE_def,UPDATE_COMMUTES,not_reg_eq,
    mode_reg2num_lt,num2register_11]);

val REG_WRITE_WRITE_PC = store_thm("REG_WRITE_WRITE_PC",
  `!r m1 m2 n d p.
     REG_WRITE (REG_WRITE r m1 15w p) m2 n d =
       if n = 15w then
         REG_WRITE r usr 15w d
       else
         REG_WRITE (REG_WRITE r m2 n d) usr 15w p`,
  RW_TAC std_ss [TO_WRITE_READ6,REG_WRITE_WRITE]
    \\ ASM_SIMP_TAC std_ss [REG_WRITE_def,UPDATE_COMMUTES,not_pc,
         mode_reg2num_15,mode_reg2num_lt,num2register_11]);

val REG_READ_WRITE = store_thm("REG_READ_WRITE",
  `(!r m n1 n2 d. REG_READ6 (REG_WRITE r m n1 d) m n2 =
      if n1 = n2 then d else REG_READ6 r m n2) /\
    !r m n d. (REG_WRITE r m n (REG_READ6 r m n) = r)`,
  RW_TAC std_ss [REG_READ6_def,REG_READ_def,REG_WRITE_def,FETCH_PC_def,
    APPLY_UPDATE_ID,mode_reg2num_15] \\ SIMP_TAC std_ss [UPDATE_def]
    \\ PROVE_TAC [r15,not_pc,not_reg_eq,mode_reg2num_lt,num2register_11,
         DECIDE ``15 < 31``]);

val REG_READ_WRITE_PC = save_thm("REG_READ_WRITE_PC",
  let val thm = (SPEC_ALL o CONJUNCT1) REG_READ_WRITE in
    CONJ
      ((SIMP_RULE arith_ss [TO_WRITE_READ6] o INST [`n2` |-> `15w`]) thm)
      ((SIMP_RULE arith_ss [TO_WRITE_READ6] o INST [`n1` |-> `15w`]) thm)
  end);

val REG_READ_WRITE_NEQ = store_thm("REG_READ_WRITE_NEQ",
  `!r m1 m2 n1 n2 d. ~(n1 = n2) ==>
      (REG_READ6 (REG_WRITE r m1 n1 d) m2 n2 = REG_READ6 r m2 n2)`,
  RW_TAC std_ss [REG_READ6_def,REG_READ_def,REG_WRITE_def,FETCH_PC_def,
    APPLY_UPDATE_ID,mode_reg2num_15] \\ SIMP_TAC std_ss [UPDATE_def]
    \\ PROVE_TAC [r15,not_pc,not_reg_eq,mode_reg2num_lt,num2register_11,
         DECIDE ``15 < 31``]);

val REG_READ6_TO_READ_SUB8 = store_thm("REG_READ6_TO_READ_SUB8",
  `!r m n. REG_READ6 r m n = REG_READ (SUB8_PC r) m n`,
  RW_TAC bool_ss [TO_WRITE_READ6,READ_TO_READ6,REG_READ_WRITE]);

val SUB8_INV = store_thm("SUB8_INV",
  `!r. SUB8_PC (ADD8_PC r) = r`,
  RW_TAC std_ss [SUB8_PC_def,ADD8_PC_def,UPDATE_EQ]
    \\ REWRITE_TAC [FUN_EQ_THM]
    \\ RW_TAC std_ss [UPDATE_def,WORD_ADD_SUB]);

(* ------------------------------------------------------------------------- *)

val IF_NEG = store_thm("IF_NEG",
  `!a b c. (if ~a then b else c) = (if a then c else b)`, PROVE_TAC []);

val UP_DOWN_THM = store_thm("UP_DOWN_THM",
  `!b x y. (if b then x + y else x - y) = UP_DOWN b x y`,
  RW_TAC bool_ss [UP_DOWN_def]);

(* ------------------------------------------------------------------------- *)

val DECODE_INST_NOT_UNEXEC = store_thm("DECODE_INST_NOT_UNEXEC",
  `!n. ~(DECODE_INST n = unexec)`, RW_TAC std_ss [DECODE_INST_def]);

val tac = Cases
  \\ RW_TAC bool_ss [combinTheory.o_THM,MIN_DEF,DECODE_INST_def,BITS_COMP_THM2,
       MOD_DIMINDEX,w2w_def,w2n_n2w,word_extract_def,word_bits_n2w]
  \\ FULL_SIMP_TAC (fcp_ss++SIZES_ss++ARITH_ss)
      [BIT_def,BITS_COMP_THM2,n2w_def];

val DATA_PROC_IMP_NOT_BIT4 = store_thm("DATA_PROC_IMP_NOT_BIT4",
  `!i. (DECODE_INST i = data_proc) /\ ~(i %% 25) ==>
         ~(((11 >< 0) i):word12 %% 4)`, tac);

val REG_SHIFT_IMP_BITS = store_thm("REG_SHIFT_IMP_BITS",
  `!i. (DECODE_INST i = reg_shift) ==>
        ~(i %% 25) /\ ((11 >< 0) i):word12 %% 4`, tac);

val LDR_IMP_BITS = store_thm("LDR_IMP_BITS",
  `!i. (DECODE_INST i = ldr) ==> (i %% 20)`,
  RW_TAC arith_ss [DECODE_INST_def]);

val STR_IMP_BITS = store_thm("STR_IMP_BITS",
  `!i. (DECODE_INST i = str) ==> ~(i %% 20)`,
  RW_TAC arith_ss [DECODE_INST_def]);

val DECODE_INST_LDM = store_thm("DECODE_INST_LDM",
  `!i. (DECODE_INST i = ldm) ==> i %% 20`,
  RW_TAC arith_ss [DECODE_INST_def]);

val DECODE_INST_STM = store_thm("DECODE_INST_STM",
  `!i. (DECODE_INST i = stm) ==> ~(i %% 20)`,
  RW_TAC arith_ss [DECODE_INST_def]);

(* ------------------------------------------------------------------------- *)

val n2w_mod32 = (REWRITE_RULE [dimword_def,dimindex_32] o
  Thm.INST_TYPE [alpha |-> ``:32``]) n2w_mod;

val ALUOUT_ALU_logic = store_thm("ALUOUT_ALU_logic",
  `!a. SND (ALU_logic a) = a`,
  SIMP_TAC std_ss [ALU_logic_def]);

val NZ_ALU_logic = store_thm("NZ_ALU_logic",
  `(!a. FST (FST (ALU_logic a)) = word_msb a) /\
   (!a. FST (SND (FST (ALU_logic a))) = (a = 0w))`,
  SIMP_TAC std_ss [ALU_logic_def]);

val ALUOUT_ADD = store_thm("ALUOUT_ADD",
  `!a b. SND (ADD a b F) = a + b`,
  SIMP_TAC arith_ss [ADD_def,ALU_arith_def,DIVMOD_2EXP,word_add_def]
    \\ SIMP_TAC bool_ss [n2w_mod32,MOD_2EXP_def]);

val NZ_ADD_lem = prove(
  `!c. (!a b. FST (FST (ADD a b c)) = word_msb (SND (ADD a b c))) /\
        !a b. FST (SND (FST (ADD a b c))) = (SND (ADD a b c) = 0w)`,
  SIMP_TAC (std_ss++SIZES_ss) [ADD_def,ALU_arith_def,DIVMOD_2EXP,
    MOD_MOD,MOD_2EXP_def,n2w_11]);

val NZ_ADD = save_thm("NZ_ADD",
  (REWRITE_RULE [ALUOUT_ADD] o SPEC `F`) NZ_ADD_lem);

val ALUOUT_ADD_CARRY = store_thm("ALUOUT_ADD_CARRY",
  `!a b. SND (ADD a b T) = a + b + 1w`,
  REWRITE_TAC [GSYM WORD_ADD_ASSOC]
    \\ SIMP_TAC arith_ss [dimword_def,ADD_def,ALU_arith_def,DIVMOD_2EXP,
         w2n_n2w,word_add_def]
    \\ SIMP_TAC bool_ss [n2w_mod32,MOD_PLUS_RIGHT,MOD_2EXP_def,ZERO_LT_TWOEXP]
    \\ SIMP_TAC bool_ss [dimword_def,n2w_11,MOD_PLUS_RIGHT,ZERO_LT_TWOEXP]);

val ALUOUT_SUB = store_thm("ALUOUT_SUB",
  `!a b. SND (SUB a b T) = a - b`,
  SIMP_TAC std_ss
    [SUB_def,ALUOUT_ADD_CARRY,WORD_NOT,GSYM WORD_ADD_SUB_ASSOC,WORD_SUB_ADD]
    \\ REWRITE_TAC [word_sub_def]);

val NZ_SUB_lem = prove(
  `!c. (!a b. FST (FST (SUB a b c)) = word_msb (SND (SUB a b c))) /\
        !a b. FST (SND (FST (SUB a b c))) = (SND (SUB a b c) = 0w)`,
  SIMP_TAC (std_ss++SIZES_ss) [SUB_def,ADD_def,ALU_arith_def,DIVMOD_2EXP,
    MOD_MOD,MOD_2EXP_def,n2w_11]);

val NZ_SUB = save_thm("NZ_SUB",
  (REWRITE_RULE [ALUOUT_SUB] o SPEC `T`) NZ_SUB_lem);

(* ------------------------------------------------------------------------- *)

val lem = prove(
  `!n wl. 0 < wl /\ ~(wl - 1 < n) ==> (n MOD wl = n)`,
  RW_TAC bool_ss [NOT_LESS,LESS_MOD,
    DECIDE ``0 < wl /\ n <= wl - 1 ==> n < wl``]);

val SLICE_ROR_THM = store_thm("SLICE_ROR_THM",
  `!h l a. ((h '' l) a) #>> l = (h -- l) a`,
  REPEAT STRIP_TAC \\ Cases_on `l = 0`
    >- ASM_REWRITE_TAC [WORD_SLICE_BITS_THM,SHIFT_ZERO]
    \\ Cases_on `a`
    \\ RW_TAC arith_ss [MIN_DEF,word_slice_n2w,word_bits_n2w,BITS_COMP_THM2,
         SLICE_THM,w2n_n2w]
    THENL [
      Cases_on `h < l` >- ASM_SIMP_TAC arith_ss [BITS_ZERO,ZERO_SHIFT]
        \\ `l <= dimindex (:'a) - 1` by DECIDE_TAC,
      Cases_on `dimindex (:'a) - 1 < l`
        >- ASM_SIMP_TAC arith_ss [BITS_ZERO,ZERO_SHIFT]]
    \\ RW_TAC arith_ss [BITS_ZERO3,ADD1,lem,word_ror_n2w,
         ZERO_LT_TWOEXP,ONCE_REWRITE_RULE [MULT_COMM] MOD_EQ_0]
    \\ ASM_SIMP_TAC arith_ss [BITS_SLICE_THM2,
          (GSYM o ONCE_REWRITE_RULE [MULT_COMM]) SLICE_THM]);

val SHIFT_ALIGN = store_thm("SHIFT_ALIGN",
  `!x:word32. w2n (8w:word8 * w2w (((1 >< 0) x):word2)) =
              8 * w2n (((1 >< 0) x):word2)`,
  STRIP_TAC \\ ISPEC_THEN `((1 >< 0) x):word2` ASSUME_TAC w2n_lt
    \\ FULL_SIMP_TAC (arith_ss++SIZES_ss) [w2w_def,word_mul_n2w,w2n_n2w]);

(* ------------------------------------------------------------------------- *)

fun Cases_on_nzcv tm =
  FULL_STRUCT_CASES_TAC (SPEC tm (armLib.tupleCases
  ``(n,z,c,v):bool#bool#bool#bool``));

val SET_NZCV_IDEM = store_thm("SET_NZCV_IDEM",
  `!a b c. SET_NZCV a (SET_NZCV b c) = SET_NZCV a c`,
  REPEAT STRIP_TAC \\ Cases_on_nzcv `a` \\ Cases_on_nzcv `b`
    \\ RW_TAC (fcp_ss++boolSimps.CONJ_ss++ARITH_ss++SIZES_ss)
         [SET_NZCV_def,word_modify_def]);

val DECODE_NZCV_SET_NZCV = store_thm("DECODE_NZCV_SET_NZCV",
   `(!a b c d n. (SET_NZCV (a,b,c,d) n) %% 31 = a) /\
    (!a b c d n. (SET_NZCV (a,b,c,d) n) %% 30 = b) /\
    (!a b c d n. (SET_NZCV (a,b,c,d) n) %% 29 = c) /\
    (!a b c d n. (SET_NZCV (a,b,c,d) n) %% 28 = d)`,
  RW_TAC (fcp_ss++SIZES_ss) [SET_NZCV_def,word_modify_def]);

val DECODE_IFMODE_SET_NZCV = store_thm("DECODE_IFMODE_SET_NZCV",
   `(!a n. (27 -- 8) (SET_NZCV a n) = (27 -- 8) n) /\
    (!a n. (SET_NZCV a n) %% 7 = n %% 7) /\
    (!a n. (SET_NZCV a n) %% 6 = n %% 6) /\
    (!a n. (SET_NZCV a n) %% 5 = n %% 5) /\
    (!a n. (4 >< 0) (SET_NZCV a n) = (4 >< 0) n)`,
  RW_TAC bool_ss [] \\ Cases_on_nzcv `a`
    \\ SIMP_TAC (fcp_ss++boolSimps.CONJ_ss++ARITH_ss++SIZES_ss)
         [SET_NZCV_def,word_modify_def,word_extract_def,word_bits_def]);

val DECODE_IFMODE_SET_IFMODE = store_thm("DECODE_IFMODE_SET_IFMODE",
   `(!i f m n. (SET_IFMODE i f m n) %% 7 = i) /\
    (!i f m n. (SET_IFMODE i f m n) %% 6 = f) /\
    (!i f m n. (4 >< 0) (SET_IFMODE i f m n) = mode_num m)`,
   RW_TAC (fcp_ss++ARITH_ss++SIZES_ss) [SET_IFMODE_def,word_modify_def,
     word_extract_def,word_bits_def,w2w]);

val SET_IFMODE_IDEM = store_thm("SET_IFMODE_IDEM",
  `!a b c d e f g. SET_IFMODE a b c (SET_IFMODE d e f g) = SET_IFMODE a b c g`,
  SIMP_TAC (fcp_ss++boolSimps.CONJ_ss++ARITH_ss++SIZES_ss)
    [SET_IFMODE_def,word_modify_def]);

val SET_IFMODE_NZCV_SWP = store_thm("SET_IFMODE_NZCV_SWP",
  `!a b c d e. SET_IFMODE a b c (SET_NZCV d e) =
               SET_NZCV d (SET_IFMODE a b c e)`,
  REPEAT STRIP_TAC \\ Cases_on_nzcv `d`
    \\ RW_TAC (fcp_ss++boolSimps.CONJ_ss++ARITH_ss++SIZES_ss)
         [SET_NZCV_def,SET_IFMODE_def,word_modify_def]
    \\ Cases_on `i < 5` \\ ASM_SIMP_TAC arith_ss []
    \\ Cases_on `i < 28` \\ ASM_SIMP_TAC arith_ss []);

val DECODE_NZCV_SET_IFMODE = store_thm("DECODE_NZCV_SET_IFMODE",
  `(!i f m n. (SET_IFMODE i f m n) %% 31 = n %% 31) /\
   (!i f m n. (SET_IFMODE i f m n) %% 30 = n %% 30) /\
   (!i f m n. (SET_IFMODE i f m n) %% 29 = n %% 29) /\
   (!i f m n. (SET_IFMODE i f m n) %% 28 = n %% 28) /\
   (!i f m n. (27 -- 8) (SET_IFMODE i f m n) = (27 -- 8) n) /\
   (!i f m n. (SET_IFMODE i f m n) %% 5 = n %% 5)`,
  RW_TAC (fcp_ss++boolSimps.CONJ_ss++ARITH_ss++SIZES_ss)
    [SET_IFMODE_def,word_modify_def,word_bits_def]);

val DECODE_MODE_THM = store_thm("DECODE_MODE_THM",
  `!m psr x y. DECODE_MODE ((4 >< 0) (SET_IFMODE x y m psr)) = m`,
  Cases \\ RW_TAC (arith_ss++SIZES_ss) [DECODE_IFMODE_SET_IFMODE,
    DECODE_MODE_def,mode_num_def,n2w_11]);

val DECODE_MODE_mode_num = store_thm("DECODE_MODE_mode_num",
  `!m. DECODE_MODE (mode_num m) = m`,
  Cases \\ SIMP_TAC (srw_ss()++SIZES_ss)
    [DECODE_MODE_def,mode_num_def,n2w_11]);

(* ------------------------------------------------------------------------- *)

val SPSR_READ_THM = store_thm("SPSR_READ_THM",
  `!psr mode cpsr.
     (CPSR_READ psr = cpsr) ==>
     ((if USER mode then cpsr else SPSR_READ psr mode) = SPSR_READ psr mode)`,
  RW_TAC bool_ss [CPSR_READ_def,SPSR_READ_def,mode2psr_def,USER_def]
    \\ REWRITE_TAC [mode_case_def]);

val SPSR_READ_THM2 = store_thm("SPSR_READ_THM2",
  `!psr mode cpsr.  USER mode ==> (SPSR_READ psr mode = CPSR_READ psr)`,
  METIS_TAC [SPSR_READ_THM]);

val CPSR_WRITE_READ = store_thm("CPSR_WRITE_READ",
  `(!psr m x. CPSR_READ (SPSR_WRITE psr m x) = CPSR_READ psr) /\
   (!psr x. CPSR_READ (CPSR_WRITE psr x) = x)`,
  RW_TAC bool_ss [CPSR_READ_def,CPSR_WRITE_def,SPSR_WRITE_def,UPDATE_def,
         USER_def,mode2psr_def]
    \\ Cases_on `m` \\ FULL_SIMP_TAC bool_ss [mode_case_def,psrs_distinct]);

val CPSR_READ_WRITE = store_thm("CPSR_READ_WRITE",
  `(!psr. CPSR_WRITE psr (CPSR_READ psr) = psr) /\
   (!psr mode. USER mode ==> (CPSR_WRITE psr (SPSR_READ psr mode) = psr))`,
  RW_TAC bool_ss [CPSR_READ_def,CPSR_WRITE_def,SPSR_READ_def,APPLY_UPDATE_ID,
         USER_def,mode2psr_def]
    \\ REWRITE_TAC [mode_case_def,APPLY_UPDATE_ID]);

val CPSR_WRITE_WRITE = store_thm("CPSR_WRITE_WRITE",
  `!psr a b. CPSR_WRITE (CPSR_WRITE psr a) b = CPSR_WRITE psr b`,
  SIMP_TAC bool_ss [CPSR_WRITE_def,UPDATE_EQ]);

val USER_usr = save_thm("USER_usr",
  simpLib.SIMP_PROVE bool_ss [USER_def] ``USER usr``);

val PSR_WRITE_COMM = store_thm("PSR_WRITE_COMM",
  `!psr m x y. SPSR_WRITE (CPSR_WRITE psr x) m y =
               CPSR_WRITE (SPSR_WRITE psr m y) x`,
  RW_TAC bool_ss [SPSR_WRITE_def,CPSR_WRITE_def,USER_def,mode2psr_def]
    \\ Cases_on `m`
    \\ FULL_SIMP_TAC bool_ss [mode_distinct,mode_case_def,psrs_distinct,
         UPDATE_COMMUTES]);

val SPSR_READ_WRITE = store_thm("SPSR_READ_WRITE",
  `!psr m. SPSR_WRITE psr m (SPSR_READ psr m) = psr`,
  RW_TAC std_ss [SPSR_READ_def,SPSR_WRITE_def,mode2psr_def]
    \\ Cases_on `m`
    \\ SIMP_TAC (srw_ss()) [APPLY_UPDATE_ID]);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
