(* ========================================================================= *)
(* FILE          : arm_rulesScript.sml                                       *)
(* DESCRIPTION   : Derived rules for the ARM Instruction Set Model           *)
(*                                                                           *)
(* AUTHORS       : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2006                                                      *)
(* ========================================================================= *)

(* interactive use:
  app load ["wordsLib", "armTheory", "armLib", "arm_evalTheory"];
*)

open HolKernel boolLib Parse bossLib;
open Q arithmeticTheory bitTheory wordsTheory wordsLib;
open armTheory arm_evalTheory simTheory lemmasTheory;

val _ = new_theory "arm_rules";

(* ------------------------------------------------------------------------- *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

val FST_COND_RAND = ISPEC `FST` COND_RAND;
val SND_COND_RAND = ISPEC `SND` COND_RAND;

fun hd_tl l = (hd l, tl l);

(* ------------------------------------------------------------------------- *)

val MOD_0 = (GSYM o REWRITE_RULE [ZERO_LT_TWOEXP] o
  SPEC `2 ** dimindex (UNIV:i32->bool)`) ZERO_MOD;

val MOD_2EXP_32 =
  simpLib.SIMP_PROVE (std_ss++wordsLib.SIZES_ss) [MOD_2EXP_def]
  ``MOD_2EXP 32 n = n MOD 2 ** dimindex (UNIV:i32->bool)``;

val MSB_lem = (GSYM o GEN_ALL o SIMP_CONV std_ss
  [BIT_def,BITS_def,MOD_2EXP_def,SUC_SUB,EXP_1,GSYM ODD_MOD2_LEM]) ``BIT x n``;

val ALU_ADD = prove(
  `!c a b. ADD a b c =
     let r = a + b + (if c then 1w else 0w) in
       ((word_msb r, r = 0w, BIT 32 (w2n a + w2n b + (if c then 1 else 0)),
        (word_msb a = word_msb b) /\ ~(word_msb a = word_msb r)), r)`,
  REPEAT STRIP_TAC \\ Cases_on_word `a` \\ Cases_on_word `b`
    \\ RW_TAC arith_ss [ADD_def,ALU_arith_def,DIVMOD_2EXP,SBIT_def,WORD_ADD_0]
    \\ SIMP_TAC std_ss [ADD_ASSOC,GSYM word_add_n2w,w2n_n2w,n2w_mod,
         MOD_2EXP_32,MOD_PLUS,ZERO_LT_TWOEXP]
    \\ ONCE_REWRITE_TAC [MOD_0]
    \\ REWRITE_TAC [GSYM n2w_11,GSYM word_add_n2w,n2w_mod]
    \\ METIS_TAC [MSB_lem]);

val ALU_ADD_NO_CARRY =
  (SIMP_RULE bossLib.arith_ss [WORD_ADD_0] o SPEC `F`) ALU_ADD;

val ALU_ADD_CARRY =
  (SIMP_RULE bossLib.arith_ss [] o SPEC `T`) ALU_ADD;

(* ......................................................................... *)

val n2w_2EXP_32 =
  (EQT_ELIM o EVAL) ``n2w (2 ** dimindex (UNIV:i32->bool)) = 0w:word32``;

val n2w_sub1 = EVAL
 ``n2w (2 ** dimindex (UNIV:i32->bool) -
  1 MOD 2 ** dimindex (UNIV:i32->bool))``;

val ALU_SUB = prove(
  `!c a b. SUB a b c =
     let r = a - b - (if c then 0w else 1w) in
       ((word_msb r, r = 0w,
         if c then
           a >=+ b
         else
           BIT 32 (w2n a + w2n ($- b) + (2 ** 32 - 1)) \/ (b = 0w),
         ~(word_msb a = word_msb b) /\ ~(word_msb a = word_msb r)), r)`,
  REPEAT STRIP_TAC \\ Cases_on_word `a` THEN Cases_on_word `b`
    \\ RW_TAC arith_ss [word_sub_def,GSYM word_add_n2w,word_2comp_n2w,
         n2w_mod,w2n_n2w,word_hs_def,WORD_SUB_RZERO,WORD_ADD_SUB,WORD_ADD_0,
         SUB_def,ALU_arith_neg_def,DIVMOD_2EXP,SBIT_def,GSYM MOD_0,MOD_2EXP_32,
         nzcv_def,n2w_2EXP_32,MSB_lem,n2w_sub1,
         (GEN_ALL o SYM o REWRITE_RULE [GSYM MOD_0] o
          INST [`n` |-> `0`] o SPEC_ALL o INST_TYPE [`:'a` |-> `:i32`]) n2w_11]
    \\ METIS_TAC [GSYM dimindex_32,WORD_ADD_ASSOC]);

val ALU_SUB_NO_CARRY =
  (SIMP_RULE bossLib.arith_ss [] o SPEC `F`) ALU_SUB;

val ALU_SUB_CARRY = (SIMP_RULE arith_ss
  [WORD_SUB_RZERO,WORD_EQ_SUB_RADD,WORD_ADD_0,WORD_HIGHER_EQ] o
  SPEC `T`) ALU_SUB;

(* ------------------------------------------------------------------------- *)

val basic_context =
  [``Abbrev (Reg = REG_READ s.registers mode)``,
   ``Abbrev (mode = DECODE_MODE ((4 >< 0) (cpsr:word32)))``,
   ``Abbrev (cpsr = CPSR_READ s.psrs)``,
   ``CONDITION_PASSED3 (NZCV cpsr) c``,
   ``~s.undefined``];

fun cntxt c i = list_mk_conj
  (mk_eq(``s.memory ((31 >< 2) (s.registers r15))``,i):: (c @ basic_context));

val word_index = METIS_PROVE [word_index_n2w]
  ``!i n. i < dimindex (UNIV:'a->bool) ==>
      ((n2w n):bool ** 'a %% i = BIT i n)``;

val CARRY_NZCV = METIS_PROVE [CARRY_def,NZCV_def] ``CARRY (NZCV x) = x %% 29``;

val REG_READ_READ6 = store_thm("REG_READ_READ6",
  `!r m n. ~(n = 15w) ==> (REG_READ6 r m n = REG_READ r m n)`,
  SIMP_TAC bool_ss [coreTheory.REG_READ6_def]);

val REG_READ_WRITE_PC =
  (GEN_ALL o SIMP_RULE std_ss [REG_READ_READ6] o INST [`n2` |-> `n`] o
   DISCH `~(n2 = 15w)` o CONJUNCT2) lemmasTheory.REG_READ_WRITE_PC;

val REG_READ_INC_PC = store_thm("REG_READ_INC_PC",
  `!r m n. ~(n = 15w) ==> (REG_READ (INC_PC r) m n = REG_READ r m n)`,
  SIMP_TAC bool_ss [lemmasTheory.TO_WRITE_READ6,REG_READ_WRITE_PC]);

val REG_WRITE_INC_PC = store_thm("REG_WRITE_INC_PC",
  `!r m n. ~(n = 15w) ==>
      (REG_WRITE (INC_PC r) m n d = INC_PC (REG_WRITE r m n d))`,
  SIMP_TAC bool_ss [TO_WRITE_READ6,REG_READ_WRITE_NEQ,REG_WRITE_WRITE_PC]);

val REG_READ_WRITE =
  (GEN_ALL o SIMP_RULE std_ss [REG_READ_READ6] o
   DISCH `~(n = 15w)` o SPEC_ALL o CONJUNCT2) lemmasTheory.REG_READ_WRITE;

fun DISCH_AND_IMP t =
  (GEN_ALL o SIMP_RULE std_ss [REG_WRITE_INC_PC,AND_IMP_INTRO] o
   DISCH t o SPEC_ALL);

val PC_ss = rewrites
  [lemmasTheory.TO_WRITE_READ6,lemmasTheory.REG_WRITE_WRITE];

val SPEC_TO_PC = (SIMP_RULE (std_ss++PC_ss) [] o
   INST [`Rd` |-> `15w:word4`] o SPEC_ALL);

val ARM_ss = rewrites [NEXT_ARMe_def,EXEC_INST_def,OUT_ARM_def,DECODE_PSR_def,
  TRANSFERS_def,FETCH_PC_def,ADDR30_def,CARRY_NZCV,
  n2w_11,word_bits_n2w,w2n_w2w,BITS_THM,
  word_index,BIT_ZERO,(GEN_ALL o SPECL [`b`,`NUMERAL n`]) BIT_def,
  FST_COND_RAND,SND_COND_RAND];

fun SYMBOLIC_EVAL_CONV frag context = GEN_ALL (Thm.DISCH context (SIMP_CONV
    (srw_ss()++boolSimps.LET_ss++SIZES_ss++armLib.PBETA_ss++ARM_ss++frag)
    [Thm.ASSUME context] ``NEXT_ARMe s``));

(* ......................................................................... *)

val UNDEF_ss = rewrites [EXCEPTION_def,cond_pass_enc_swi,decode_enc_swi,
    exception2mode_def,exception2num_thm];

val ARM_UNDEF = SYMBOLIC_EVAL_CONV UNDEF_ss ``s.undefined``;

val nop_context =
  [``Abbrev (cpsr = CPSR_READ s.psrs)``,
   ``~CONDITION_PASSED3 (NZCV cpsr) c``,
   ``~s.undefined``];

fun nop_cntxt i = list_mk_conj
  (mk_eq(``s.memory ((31 >< 2) (s.registers r15))``,i):: nop_context);

(* ......................................................................... *)

val NOP_ss = rewrites [cond_pass_enc_data_proc,
  cond_pass_enc_data_proc2, cond_pass_enc_data_proc3,cond_pass_enc_coproc,
  cond_pass_enc_mla_mul,cond_pass_enc_br,cond_pass_enc_swi,
  cond_pass_enc_ldr_str,cond_pass_enc_ldm_stm,cond_pass_enc_swp];

fun eval_nop t = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  (subst [``f:condition -> bool -> bool ** i4 ->
              bool ** i4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``enc ((f:condition -> bool -> bool ** i4 ->
             bool ** i4 -> addr_mode1 -> arm_instruction) c x Rd Rm Op2)``));

val thms = map eval_nop
   [``instruction$AND``,``instruction$EOR``,``instruction$SUB``,
    ``instruction$RSB``,``instruction$ADD``,``instruction$ADC``,
    ``instruction$SBC``,``instruction$RSC``,``instruction$ORR``,
    ``instruction$BIC``];

val (ARM_AND_NOP,thms) = hd_tl thms;
val (ARM_EOR_NOP,thms) = hd_tl thms;
val (ARM_SUB_NOP,thms) = hd_tl thms;
val (ARM_RSB_NOP,thms) = hd_tl thms;
val (ARM_ADD_NOP,thms) = hd_tl thms;
val (ARM_ADC_NOP,thms) = hd_tl thms;
val (ARM_SBC_NOP,thms) = hd_tl thms;
val (ARM_RSC_NOP,thms) = hd_tl thms;
val (ARM_ORR_NOP,thms) = hd_tl thms;
val ARM_BIC_NOP = hd thms;

val ARM_MOV_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$MOV c x Rd Op2)``);

val ARM_MVN_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$MVN c x Rd Op2)``);

val ARM_TST_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$TST c Rm Op2)``);

val ARM_TEQ_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$TEQ c Rm Op2)``);

val ARM_CMP_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$CMP c Rm Op2)``);

val ARM_CMN_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$CMN c Rm Op2)``);

val ARM_MUL_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$MUL c x Rd Rs Rm)``);

val ARM_MLA_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$MLA c x Rd Rs Rm Rn)``);

val ARM_B_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$B c offset)``);

val ARM_BL_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$BL c offset)``);

val ARM_SWI_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$SWI c)``);

val ARM_UND_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$UND c)``);

val ARM_LDR_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$LDR c opt Rd Rn Op2)``);

val ARM_STR_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$STR c opt Rd Rn Op2)``);

val ARM_SWP_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$SWP c b Rd Rm Rn)``);

val ARM_LDM_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$LDM c opt Rd list)``);

val ARM_STM_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$STM c opt Rd list)``);

(* ......................................................................... *)

val LSL_NOT_ZERO = prove(
  `!n. ~(n = 0w:word5) ==> ~(w2w n = 0w:word8)`,
  Cases_word \\ RW_TAC (bool_ss++SIZES_ss)
       [ZERO_MOD,ZERO_LT_TWOEXP,w2w_def,n2w_11,w2n_n2w]
    \\ ASSUME_TAC (DECIDE ``5 < 8``) \\ IMP_RES_TAC TWOEXP_MONO
    \\ METIS_TAC [MOD_2EXP_LT,LESS_TRANS,LESS_MOD]);

val WORD_NEG_cor =
  METIS_PROVE [WORD_NEG,WORD_ADD_ASSOC,WORD_ADD_COMM,word_sub_def]
  ``~a + b + 1w = b - a``;

val WORD_1COMP_ZERO =
  METIS_PROVE [WORD_NOT_NOT,WORD_NOT_T] ``!a. (~a = 0w) = (a = Tw)``;

val DP_ss =
  rewrites [DATA_PROCESSING_def,ARITHMETIC_def,TEST_OR_COMP_def,
    ALU_def,LSL_def,LSR_def,AND_def,ORR_def,EOR_def,ALU_logic_def,SET_NZC_def,
    ADDR_MODE1_def,LSL_NOT_ZERO,WORD_NEG_cor,WORD_1COMP_ZERO,
    ALU_ADD_NO_CARRY,ALU_SUB_NO_CARRY,ALU_ADD_CARRY,ALU_SUB_CARRY,
    cond_pass_enc_data_proc, decode_enc_data_proc, decode_data_proc_enc,
    cond_pass_enc_data_proc2,decode_enc_data_proc2,decode_data_proc_enc2,
    cond_pass_enc_data_proc3,decode_enc_data_proc3,decode_data_proc_enc3,
    shift_immediate_enc,shift_immediate_shift_register];

(* ......................................................................... *)

fun eval_op c t = SYMBOLIC_EVAL_CONV DP_ss (cntxt c
  (subst [``f:condition -> bool -> bool ** i4 ->
              bool ** i4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``enc ((f:condition -> bool -> bool ** i4 ->
             bool ** i4 -> addr_mode1 -> arm_instruction)
       c F Rd Rm (Dp_shift_immediate (LSL Rn) 0w))``));

val thms = map (eval_op [])
   [``instruction$AND``,``instruction$EOR``,``instruction$SUB``,
    ``instruction$RSB``,``instruction$ADD``,``instruction$ORR``,
    ``instruction$BIC``];

val (ARM_AND,thms) = hd_tl thms;
val (ARM_EOR,thms) = hd_tl thms;
val (ARM_SUB,thms) = hd_tl thms;
val (ARM_RSB,thms) = hd_tl thms;
val (ARM_ADD,thms) = hd_tl thms;
val (ARM_ORR,thms) = hd_tl thms;
val ARM_BIC = hd thms;

val thms = map (eval_op [``~((cpsr:word32) %% 29)``])
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``]

val (ARM_ADC_CARRY,thms) = hd_tl thms;
val (ARM_SBC_CARRY,thms) = hd_tl thms;
val ARM_RSC_CARRY = hd thms;

val thms = map (eval_op [``(cpsr:word32) %% 29``])
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``]

val (ARM_ADC_NO_CARRY,thms) = hd_tl thms;
val (ARM_SBC_NO_CARRY,thms) = hd_tl thms;
val ARM_RSC_NO_CARRY = hd thms;

fun eval_op c t = SYMBOLIC_EVAL_CONV DP_ss (cntxt c
  (subst [``f:condition -> bool -> bool ** i4 ->
              bool ** i4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``enc ((f:condition -> bool -> bool ** i4 ->
             bool ** i4 -> addr_mode1 -> arm_instruction)
       c T Rd Rm (Dp_shift_immediate (LSL Rn) 0w))``));

val thms = map (eval_op [])
   [``instruction$AND``,``instruction$EOR``,``instruction$SUB``,
    ``instruction$RSB``,``instruction$ADD``,``instruction$ORR``,
    ``instruction$BIC``];

val (ARM_ANDS,thms) = hd_tl thms;
val (ARM_EORS,thms) = hd_tl thms;
val (ARM_SUBS,thms) = hd_tl thms;
val (ARM_RSBS,thms) = hd_tl thms;
val (ARM_ADDS,thms) = hd_tl thms;
val (ARM_ORRS,thms) = hd_tl thms;
val ARM_BICS = hd thms;

val thms = map (eval_op [``~((cpsr:word32) %% 29)``])
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``]

val (ARM_ADCS_CARRY,thms) = hd_tl thms;
val (ARM_SBCS_CARRY,thms) = hd_tl thms;
val ARM_RSCS_CARRY = hd thms;

val thms = map (eval_op [``(cpsr:word32) %% 29``])
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``]

val (ARM_ADCS_NO_CARRY,thms) = hd_tl thms;
val (ARM_SBCS_NO_CARRY,thms) = hd_tl thms;
val ARM_RSCS_NO_CARRY = hd thms;

(* ......................................................................... *)

fun eval_op c t = SYMBOLIC_EVAL_CONV DP_ss (cntxt (``~(n = 0w:word5)``::c)
  (subst [``f:condition -> bool -> bool ** i4 ->
              bool ** i4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``enc ((f:condition -> bool -> bool ** i4 ->
             bool ** i4 -> addr_mode1 -> arm_instruction)
       c F Rd Rm (Dp_shift_immediate (LSL Rn) n))``));

val thms = map (eval_op [])
   [``instruction$AND``,``instruction$EOR``,``instruction$SUB``,
    ``instruction$RSB``,``instruction$ADD``,``instruction$ORR``,
    ``instruction$BIC``];

val (ARM_AND_LSL,thms) = hd_tl thms;
val (ARM_EOR_LSL,thms) = hd_tl thms;
val (ARM_SUB_LSL,thms) = hd_tl thms;
val (ARM_RSB_LSL,thms) = hd_tl thms;
val (ARM_ADD_LSL,thms) = hd_tl thms;
val (ARM_ORR_LSL,thms) = hd_tl thms;
val ARM_BIC_LSL = hd thms;

val thms = map (eval_op [``~((cpsr:word32) %% 29)``])
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``]

val (ARM_ADC_LSL_CARRY,thms) = hd_tl thms;
val (ARM_SBC_LSL_CARRY,thms) = hd_tl thms;
val ARM_RSC_LSL_CARRY = hd thms;

val thms = map (eval_op [``(cpsr:word32) %% 29``])
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``]

val (ARM_ADC_LSL_NO_CARRY,thms) = hd_tl thms;
val (ARM_SBC_LSL_NO_CARRY,thms) = hd_tl thms;
val ARM_RSC_LSL_NO_CARRY = hd thms;

fun eval_op c t = SYMBOLIC_EVAL_CONV DP_ss (cntxt (``~(n = 0w:word5)``::c)
  (subst [``f:condition -> bool -> bool ** i4 ->
              bool ** i4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``enc ((f:condition -> bool -> bool ** i4 ->
             bool ** i4 -> addr_mode1 -> arm_instruction)
       c T Rd Rm (Dp_shift_immediate (LSL Rn) n))``));

val thms = map (eval_op [])
   [``instruction$AND``,``instruction$EOR``,``instruction$SUB``,
    ``instruction$RSB``,``instruction$ADD``,``instruction$ORR``,
    ``instruction$BIC``];

val (ARM_ANDS_LSL,thms) = hd_tl thms;
val (ARM_EORS_LSL,thms) = hd_tl thms;
val (ARM_SUBS_LSL,thms) = hd_tl thms;
val (ARM_RSBS_LSL,thms) = hd_tl thms;
val (ARM_ADDS_LSL,thms) = hd_tl thms;
val (ARM_ORRS_LSL,thms) = hd_tl thms;
val ARM_BICS_LSL = hd thms;

val thms = map (eval_op [``~((cpsr:word32) %% 29)``])
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``]

val (ARM_ADCS_LSL_CARRY,thms) = hd_tl thms;
val (ARM_SBCS_LSL_CARRY,thms) = hd_tl thms;
val ARM_RSCS_LSL_CARRY = hd thms;

val thms = map (eval_op [``(cpsr:word32) %% 29``])
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``]

val (ARM_ADCS_LSL_NO_CARRY,thms) = hd_tl thms;
val (ARM_SBCS_LSL_NO_CARRY,thms) = hd_tl thms;
val ARM_RSCS_LSL_NO_CARRY = hd thms;

(* ......................................................................... *)

fun eval_op c t = SYMBOLIC_EVAL_CONV DP_ss (cntxt (``~(n = 0w:word5)``::c)
  (subst [``f:condition -> bool -> bool ** i4 ->
              bool ** i4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``enc ((f:condition -> bool -> bool ** i4 ->
             bool ** i4 -> addr_mode1 -> arm_instruction)
       c F Rd Rm (Dp_shift_immediate (LSR Rn) n))``));

val thms = map (eval_op [])
   [``instruction$AND``,``instruction$EOR``,``instruction$SUB``,
    ``instruction$RSB``,``instruction$ADD``,``instruction$ORR``,
    ``instruction$BIC``];

val (ARM_AND_LSR,thms) = hd_tl thms;
val (ARM_EOR_LSR,thms) = hd_tl thms;
val (ARM_SUB_LSR,thms) = hd_tl thms;
val (ARM_RSB_LSR,thms) = hd_tl thms;
val (ARM_ADD_LSR,thms) = hd_tl thms;
val (ARM_ORR_LSR,thms) = hd_tl thms;
val ARM_BIC_LSR = hd thms;

val thms = map (eval_op [``~((cpsr:word32) %% 29)``])
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``]

val (ARM_ADC_LSR_CARRY,thms) = hd_tl thms;
val (ARM_SBC_LSR_CARRY,thms) = hd_tl thms;
val ARM_RSC_LSR_CARRY = hd thms;

val thms = map (eval_op [``(cpsr:word32) %% 29``])
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``]

val (ARM_ADC_LSR_NO_CARRY,thms) = hd_tl thms;
val (ARM_SBC_LSR_NO_CARRY,thms) = hd_tl thms;
val ARM_RSC_LSR_NO_CARRY = hd thms;

fun eval_op c t = SYMBOLIC_EVAL_CONV DP_ss (cntxt (``~(n = 0w:word5)``::c)
  (subst [``f:condition -> bool -> bool ** i4 ->
              bool ** i4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``enc ((f:condition -> bool -> bool ** i4 ->
             bool ** i4 -> addr_mode1 -> arm_instruction)
       c T Rd Rm (Dp_shift_immediate (LSR Rn) n))``));

val thms = map (eval_op [])
   [``instruction$AND``,``instruction$EOR``,``instruction$SUB``,
    ``instruction$RSB``,``instruction$ADD``,``instruction$ORR``,
    ``instruction$BIC``];

val (ARM_ANDS_LSR,thms) = hd_tl thms;
val (ARM_EORS_LSR,thms) = hd_tl thms;
val (ARM_SUBS_LSR,thms) = hd_tl thms;
val (ARM_RSBS_LSR,thms) = hd_tl thms;
val (ARM_ADDS_LSR,thms) = hd_tl thms;
val (ARM_ORRS_LSR,thms) = hd_tl thms;
val ARM_BICS_LSR = hd thms;

val thms = map (eval_op [``~((cpsr:word32) %% 29)``])
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``]

val (ARM_ADCS_LSR_CARRY,thms) = hd_tl thms;
val (ARM_SBCS_LSR_CARRY,thms) = hd_tl thms;
val ARM_RSCS_LSR_CARRY = hd thms;

val thms = map (eval_op [``(cpsr:word32) %% 29``])
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``]

val (ARM_ADCS_LSR_NO_CARRY,thms) = hd_tl thms;
val (ARM_SBCS_LSR_NO_CARRY,thms) = hd_tl thms;
val ARM_RSCS_LSR_NO_CARRY = hd thms;

(* ......................................................................... *)

val ARM_MOV = SYMBOLIC_EVAL_CONV DP_ss (cntxt []
  ``enc (instruction$MOV c F Rd (Dp_shift_immediate (LSL Rn) 0w))``);

val ARM_MVN = SYMBOLIC_EVAL_CONV DP_ss (cntxt []
  ``enc (instruction$MVN c F Rd (Dp_shift_immediate (LSL Rn) 0w))``);

val ARM_MOVS = SYMBOLIC_EVAL_CONV DP_ss (cntxt []
  ``enc (instruction$MOV c T Rd (Dp_shift_immediate (LSL Rn) 0w))``);

val ARM_MVNS = SYMBOLIC_EVAL_CONV DP_ss (cntxt []
  ``enc (instruction$MVN c T Rd (Dp_shift_immediate (LSL Rn) 0w))``);

val ARM_MOV_LSL = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  ``enc (instruction$MOV c F Rd (Dp_shift_immediate (LSL Rn) n))``);

val ARM_MOV_LSR = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  ``enc (instruction$MOV c F Rd (Dp_shift_immediate (LSR Rn) n))``);

val ARM_MVN_LSL = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  ``enc (instruction$MVN c F Rd (Dp_shift_immediate (LSL Rn) n))``);

val ARM_MVN_LSR = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  ``enc (instruction$MVN c F Rd (Dp_shift_immediate (LSR Rn) n))``);

val ARM_MOVS_LSL = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  ``enc (instruction$MOV c T Rd (Dp_shift_immediate (LSL Rn) n))``);

val ARM_MOVS_LSR = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  ``enc (instruction$MOV c T Rd (Dp_shift_immediate (LSR Rn) n))``);

val ARM_MVNS_LSL = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  ``enc (instruction$MVN c T Rd (Dp_shift_immediate (LSL Rn) n))``);

val ARM_MVNS_LSR = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  ``enc (instruction$MVN c T Rd (Dp_shift_immediate (LSR Rn) n))``);

(* ......................................................................... *)

val ARM_TST = SYMBOLIC_EVAL_CONV DP_ss (cntxt []
  ``enc (instruction$TST c Rm (Dp_shift_immediate (LSL Rn) 0w))``);

val ARM_TEQ = SYMBOLIC_EVAL_CONV DP_ss (cntxt []
  ``enc (instruction$TEQ c Rm (Dp_shift_immediate (LSL Rn) 0w))``);

val ARM_CMP = SYMBOLIC_EVAL_CONV DP_ss (cntxt []
  ``enc (instruction$CMP c Rm (Dp_shift_immediate (LSL Rn) 0w))``);

val ARM_CMN = SYMBOLIC_EVAL_CONV DP_ss (cntxt []
  ``enc (instruction$CMN c Rm (Dp_shift_immediate (LSL Rn) 0w))``);

(* ......................................................................... *)

val MLA_MUL_ss =
  rewrites [MLA_MUL_def,ALU_multiply_def,SET_NZC_def,REG_READ_INC_PC,
    cond_pass_enc_mla_mul,decode_enc_mla_mul,decode_mla_mul_enc];

val ARM_MUL = SYMBOLIC_EVAL_CONV MLA_MUL_ss (cntxt
  [``~(Rd = 15w:word4)``,``~(Rs = 15w:word4)``,``~(Rd = Rs:word4)``]
  ``enc (instruction$MUL c F Rd Rs Rm)``);

val ARM_MLA = SYMBOLIC_EVAL_CONV MLA_MUL_ss (cntxt
  [``~(Rd = 15w:word4)``,``~(Rs = 15w:word4)``,``~(Rd = Rs:word4)``]
  ``enc (instruction$MLA c F Rd Rs Rm Rn)``);

val ARM_MULS = SYMBOLIC_EVAL_CONV MLA_MUL_ss (cntxt
  [``~(Rd = 15w:word4)``,``~(Rs = 15w:word4)``,``~(Rd = Rs:word4)``]
  ``enc (instruction$MUL c T Rd Rs Rm)``);

val ARM_MLAS = SYMBOLIC_EVAL_CONV MLA_MUL_ss (cntxt
  [``~(Rd = 15w:word4)``,``~(Rs = 15w:word4)``,``~(Rd = Rs:word4)``]
  ``enc (instruction$MLA c T Rd Rs Rm Rn)``);

(* ......................................................................... *)

val BRANCH_ss =
  rewrites [BRANCH_def,REG_READ_def,
    cond_pass_enc_br,decode_enc_br,decode_br_enc];

val ARM_B = SYMBOLIC_EVAL_CONV BRANCH_ss (list_mk_conj
  [``s.memory ((31 >< 2) (s.registers r15)) = enc (instruction$B c offset)``,
   ``CONDITION_PASSED3 (NZCV (CPSR_READ s.psrs)) c``,
   ``~s.undefined``]);

val ARM_BL = SYMBOLIC_EVAL_CONV BRANCH_ss (list_mk_conj
  [``s.memory ((31 >< 2) (s.registers r15)) = enc (instruction$BL c offset)``,
   ``Abbrev (mode = DECODE_MODE ((4 >< 0) (cpsr:word32)))``,
   ``Abbrev (cpsr = CPSR_READ s.psrs)``,
   ``CONDITION_PASSED3 (NZCV cpsr) c``,
   ``~s.undefined``]);

(* ......................................................................... *)

val SWI_EX_ss =
  rewrites [EXCEPTION_def,exception2mode_def,exception2num_thm,
    cond_pass_enc_swi,decode_enc_swi,cond_pass_enc_coproc,decode_enc_coproc];

val ARM_SWI = SYMBOLIC_EVAL_CONV SWI_EX_ss (list_mk_conj
  [``s.memory ((31 >< 2) (s.registers r15)) = enc (instruction$SWI c)``,
   ``Abbrev (cpsr = CPSR_READ s.psrs)``,
   ``CONDITION_PASSED3 (NZCV cpsr) c``,
   ``~s.undefined``]);

val ARM_UND = SYMBOLIC_EVAL_CONV SWI_EX_ss (list_mk_conj
  [``s.memory ((31 >< 2) (s.registers r15)) = enc (instruction$UND c)``,
   ``Abbrev (cpsr = CPSR_READ s.psrs)``,
   ``CONDITION_PASSED3 (NZCV cpsr) c``,
   ``~s.undefined``]);

(* ......................................................................... *)

val UP_DOWN_ZERO = (GEN_ALL o SIMP_RULE std_ss [UP_DOWN_def] o
  METIS_PROVE [UP_DOWN_def,WORD_SUB_RZERO,WORD_ADD_0]) ``UP_DOWN u x 0w = x``;

val LDR_STR_ss =
  rewrites [LDR_STR_def,ADDR_MODE2_def,MEM_WRITE_def,BW_READ_def,UP_DOWN_def,
    listTheory.HD,rich_listTheory.SNOC,word_bits_n2w,w2w_n2w,BITS_THM,
    WORD_ADD_0,REG_WRITE_INC_PC,REG_READ_WRITE,REG_READ_INC_PC,UP_DOWN_ZERO,
    LSL_def,LSR_def,LSL_NOT_ZERO,immediate_enc2,shift_immediate_enc2,
    cond_pass_enc_ldr_str,decode_enc_ldr_str,decode_ldr_str_enc];

val ARM_LDR = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rn = 15w:word4)``]
  ``enc (instruction$LDR c <| Pre := T; Up := u; BSN := F; Wb := w |>
         Rd Rn (Dt_immediate 0w))``);

val ARM_LDR_POST_UP_IMM = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rn = 15w:word4)``]
  ``enc (instruction$LDR c <| Pre := F; Up := T; BSN := F; Wb := w |>
         Rd Rn (Dt_immediate offset))``);

val ARM_LDR_POST_UP_REG = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rn = 15w:word4)``]
  ``enc (instruction$LDR c <| Pre := F; Up := T; BSN := F; Wb := w |>
         Rd Rn (Dt_shift_immediate (LSL Rm) 0w))``);

val ARM_LDR_POST_UP_LSL_REG = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rn = 15w:word4)``,``~(sh = 0w:word5)``]
  ``enc (instruction$LDR c <| Pre := F; Up := T; BSN := F; Wb := w |>
         Rd Rn (Dt_shift_immediate (LSL Rm) sh))``);

val ARM_LDR_PRE_UP_WB_IMM = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rn = 15w:word4)``]
  ``enc (instruction$LDR c <| Pre := T; Up := T; BSN := F; Wb := T |>
         Rd Rn (Dt_immediate offset))``);

val ARM_LDR_PRE_UP_WB_REG = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rn = 15w:word4)``]
  ``enc (instruction$LDR c <| Pre := T; Up := T; BSN := F; Wb := T |>
         Rd Rn (Dt_shift_immediate (LSL Rm) 0w))``);

val ARM_LDR_PRE_UP_WB_LSL_REG = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rn = 15w:word4)``,``~(sh = 0w:word5)``]
  ``enc (instruction$LDR c <| Pre := T; Up := T; BSN := F; Wb := T |>
         Rd Rn (Dt_shift_immediate (LSL Rm) sh))``);

val ARM_STR = SYMBOLIC_EVAL_CONV LDR_STR_ss
  (cntxt [``~(Rd = 15w:word4)``, ``~(Rn = 15w:word4)``]
  ``enc (instruction$STR c <| Pre := T; Up := u; BSN := F; Wb := w |>
         Rd Rn (Dt_immediate 0w))``);

val ARM_STR_POST_UP_IMM = SYMBOLIC_EVAL_CONV LDR_STR_ss
  (cntxt [``~(Rd = 15w:word4)``, ``~(Rn = 15w:word4)``]
  ``enc (instruction$STR c <| Pre := F; Up := T; BSN := F; Wb := w |>
         Rd Rn (Dt_immediate offset))``);

val ARM_STR_PRE_UP_WB_IMM = SYMBOLIC_EVAL_CONV LDR_STR_ss
  (cntxt [``~(Rd = 15w:word4)``,``~(Rn = 15w:word4)``]
  ``enc (instruction$STR c <| Pre := T; Up := T; BSN := F; Wb := T |>
         Rd Rn (Dt_immediate offset))``);

val ARM_STR_POST_UP_REG = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rd = 15w:word4)``,``~(Rm = 15w:word4)``,``~(Rn = 15w:word4)``]
  ``enc (instruction$STR c <| Pre := F; Up := T; BSN := F; Wb := w |>
         Rd Rn (Dt_shift_immediate (LSL Rm) 0w))``);

val ARM_STR_PRE_UP_WB_REG = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rd = 15w:word4)``,``~(Rm = 15w:word4)``,``~(Rn = 15w:word4)``]
  ``enc (instruction$STR c <| Pre := T; Up := T; BSN := F; Wb := T |>
         Rd Rn (Dt_shift_immediate (LSL Rm) 0w))``);

val ARM_STR_POST_UP_LSL_REG = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rd = 15w:word4)``,``~(Rm = 15w:word4)``,
         ``~(Rn = 15w:word4)``,``~(sh = 0w:word5)``]
  ``enc (instruction$STR c <| Pre := F; Up := T; BSN := F; Wb := w |>
         Rd Rn (Dt_shift_immediate (LSL Rm) sh))``);

val ARM_STR_PRE_UP_WB_LSL_REG = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rd = 15w:word4)``,``~(Rm = 15w:word4)``,
         ``~(Rn = 15w:word4)``,``~(sh = 0w:word5)``]
  ``enc (instruction$STR c <| Pre := T; Up := T; BSN := F; Wb := T |>
         Rd Rn (Dt_shift_immediate (LSL Rm) sh))``);

(* ......................................................................... *)

val ARM_LDR_BYTE = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rn = 15w:word4)``]
  ``enc (instruction$LDR c <| Pre := T; Up := u; BSN := T; Wb := w |>
         Rd Rn (Dt_immediate 0w))``);

val ARM_LDR_BYTE_POST_UP_IMM = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rn = 15w:word4)``]
  ``enc (instruction$LDR c <| Pre := F; Up := T; BSN := T; Wb := w |>
         Rd Rn (Dt_immediate offset))``);

val ARM_LDR_BYTE_PRE_UP_WB_IMM = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rn = 15w:word4)``]
  ``enc (instruction$LDR c <| Pre := T; Up := T; BSN := T; Wb := T |>
         Rd Rn (Dt_immediate offset))``);

val ARM_LDR_BYTE_POST_UP_REG = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rn = 15w:word4)``]
  ``enc (instruction$LDR c <| Pre := F; Up := T; BSN := T; Wb := w |>
         Rd Rn (Dt_shift_immediate (LSL Rm) 0w))``);

val ARM_LDR_BYTE_PRE_UP_WB_REG = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rn = 15w:word4)``]
  ``enc (instruction$LDR c <| Pre := T; Up := T; BSN := T; Wb := T |>
         Rd Rn (Dt_shift_immediate (LSL Rm) 0w))``);

val ARM_LDR_BYTE_POST_UP_LSL_REG = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rn = 15w:word4)``,``~(sh = 0w:word5)``]
  ``enc (instruction$LDR c <| Pre := F; Up := T; BSN := T; Wb := w |>
         Rd Rn (Dt_shift_immediate (LSL Rm) sh))``);

val ARM_LDR_BYTE_PRE_UP_WB_LSL_REG = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rn = 15w:word4)``,``~(sh = 0w:word5)``]
  ``enc (instruction$LDR c <| Pre := T; Up := T; BSN := T; Wb := T |>
         Rd Rn (Dt_shift_immediate (LSL Rm) sh))``);

val ARM_STR_BYTE = SYMBOLIC_EVAL_CONV LDR_STR_ss
  (cntxt [``~(Rd = 15w:word4)``, ``~(Rn = 15w:word4)``]
  ``enc (instruction$STR c <| Pre := T; Up := u; BSN := T; Wb := w |>
         Rd Rn (Dt_immediate 0w))``);

val ARM_STR_BYTE_POST_UP_IMM = SYMBOLIC_EVAL_CONV LDR_STR_ss
  (cntxt [``~(Rd = 15w:word4)``, ``~(Rn = 15w:word4)``]
  ``enc (instruction$STR c <| Pre := F; Up := T; BSN := T; Wb := w |>
         Rd Rn (Dt_immediate offset))``);

val ARM_STR_BYTE_PRE_UP_WB_IMM = SYMBOLIC_EVAL_CONV LDR_STR_ss
  (cntxt [``~(Rd = 15w:word4)``,``~(Rn = 15w:word4)``]
  ``enc (instruction$STR c <| Pre := T; Up := T; BSN := T; Wb := T |>
         Rd Rn (Dt_immediate offset))``);

val ARM_STR_BYTE_POST_UP_REG = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rd = 15w:word4)``,``~(Rm = 15w:word4)``,``~(Rn = 15w:word4)``]
  ``enc (instruction$STR c <| Pre := F; Up := T; BSN := T; Wb := w |>
         Rd Rn (Dt_shift_immediate (LSL Rm) 0w))``);

val ARM_STR_BYTE_PRE_UP_WB_REG = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rd = 15w:word4)``,``~(Rm = 15w:word4)``,``~(Rn = 15w:word4)``]
  ``enc (instruction$STR c <| Pre := T; Up := T; BSN := T; Wb := T |>
         Rd Rn (Dt_shift_immediate (LSL Rm) 0w))``);

val ARM_STR_BYTE_POST_UP_LSL_REG = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rd = 15w:word4)``,``~(Rm = 15w:word4)``,
         ``~(Rn = 15w:word4)``,``~(sh = 0w:word5)``]
  ``enc (instruction$STR c <| Pre := F; Up := T; BSN := T; Wb := w |>
         Rd Rn (Dt_shift_immediate (LSL Rm) sh))``);

val ARM_STR_BYTE_PRE_UP_WB_LSL_REG = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [``~(Rd = 15w:word4)``,``~(Rm = 15w:word4)``,
         ``~(Rn = 15w:word4)``,``~(sh = 0w:word5)``]
  ``enc (instruction$STR c <| Pre := T; Up := T; BSN := T; Wb := T |>
         Rd Rn (Dt_shift_immediate (LSL Rm) sh))``);

(* ......................................................................... *)

val SWP_ss =
  rewrites [SWP_def,MEM_WRITE_def,BW_READ_def,
    listTheory.HD,rich_listTheory.SNOC,word_bits_n2w,w2w_n2w,BITS_THM,
    WORD_ADD_0,REG_WRITE_INC_PC,REG_READ_WRITE,REG_READ_INC_PC,
    cond_pass_enc_swp,decode_enc_swp,decode_swp_enc];

val ARM_SWP = SYMBOLIC_EVAL_CONV SWP_ss (cntxt [``~(Rm = 15w:word4)``]
  ``enc (instruction$SWP c F Rd Rm Rn)``);

val ARM_SWP_BYTE = SYMBOLIC_EVAL_CONV SWP_ss (cntxt [``~(Rm = 15w:word4)``]
  ``enc (instruction$SWP c T Rd Rm Rn)``);

(* ......................................................................... *)

val TRANSFER_LDM = prove(
  `!m d l. FST (TRANSFERS m d (MAP MemRead l)) = m`,
  Induct_on `l` \\ ASM_SIMP_TAC (srw_ss()++listSimps.LIST_ss) [TRANSFERS_def]);

val TRANSFER_LDM2_lem = prove(
  `!m d l. LENGTH (SND (TRANSFERS m d (MAP MemRead l))) = LENGTH d + LENGTH l`,
  Induct_on `l` \\ ASM_SIMP_TAC (srw_ss()++listSimps.LIST_ss++ARITH_ss)
    [TRANSFERS_def,rich_listTheory.LENGTH_SNOC]);

val TRANSFER_LDM2_lem2 = prove(
  `!m rd l. LENGTH (SND (TRANSFERS m []
             (MAP MemRead (ADDRESS_LIST rd (LENGTH l))))) = LENGTH l`,
   SIMP_TAC list_ss [TRANSFER_LDM2_lem,ADDRESS_LIST_def,
     rich_listTheory.LENGTH_GENLIST]);

val TRANSFER_LDM2_lem3 = prove(
  `!m d l. SND (TRANSFERS m d (MAP MemRead l)) = d ++ MAP (\x. m (ADDR30 x)) l`,
 Induct_on `l` \\ ASM_SIMP_TAC (srw_ss()++listSimps.LIST_ss)
   [TRANSFERS_def,my_listTheory.APPEND_SNOC1]);

val TRANSFER_LDM2 = prove(
  `!m d l. FIRSTN (LENGTH l)
             (SND (TRANSFERS m [] (MAP MemRead (ADDRESS_LIST rd (LENGTH l))))) =
           GENLIST (\i. m (ADDR30 (rd + 4w * n2w i))) (LENGTH l)`,
  REPEAT STRIP_TAC
    \\ `FIRSTN (LENGTH l)
          (SND (TRANSFERS m [] (MAP MemRead (ADDRESS_LIST rd (LENGTH l))))) =
           SND (TRANSFERS m [] (MAP MemRead (ADDRESS_LIST rd (LENGTH l))))`
    by METIS_TAC [TRANSFER_LDM2_lem2,rich_listTheory.FIRSTN_LENGTH_ID]
    \\ ASM_SIMP_TAC list_ss [ADDRESS_LIST_def,TRANSFER_LDM2_lem3,
         my_listTheory.MAP_GENLIST]
    \\ MATCH_MP_TAC my_listTheory.GENLIST_FUN_EQ
    \\ SIMP_TAC std_ss []);

val TRANSFER_LDM2 = prove(
  `!m d l. FIRSTN (LENGTH l)
             (SND (TRANSFERS m [] (MAP MemRead (ADDRESS_LIST rd (LENGTH l))))) =
           MAP (m o ADDR30) (ADDRESS_LIST rd (LENGTH l))`,
  REPEAT STRIP_TAC
    \\ `FIRSTN (LENGTH l)
          (SND (TRANSFERS m [] (MAP MemRead (ADDRESS_LIST rd (LENGTH l))))) =
           SND (TRANSFERS m [] (MAP MemRead (ADDRESS_LIST rd (LENGTH l))))`
    by METIS_TAC [TRANSFER_LDM2_lem2,rich_listTheory.FIRSTN_LENGTH_ID]
    \\ ASM_SIMP_TAC list_ss [ADDRESS_LIST_def,TRANSFER_LDM2_lem3,
         my_listTheory.MAP_GENLIST]
    \\ MATCH_MP_TAC my_listTheory.GENLIST_FUN_EQ
    \\ SIMP_TAC std_ss []);

val TRANSFER_STM = prove(
  `!m d r mode rd l. FST (TRANSFERS m d (STM_LIST r mode l)) =
      FOLDL (\mem (rp,rd). MEM_WRITE F mem rd (REG_READ r mode rp)) m l`,
  Induct_on `l` \\ TRY (Cases_on `h`)
    \\ ASM_SIMP_TAC (srw_ss()++listSimps.LIST_ss) [TRANSFERS_def,STM_LIST_def]
    \\ ASM_SIMP_TAC std_ss [GSYM STM_LIST_def]);

val LDM_STM_ss =
  rewrites [LDM_STM_def,ADDR_MODE4_def,MEM_WRITE_def,BW_READ_def,UP_DOWN_def,
    FIRST_ADDRESS_def,WB_ADDRESS_def,rich_listTheory.FIRSTN_LENGTH_ID,
    listTheory.HD,rich_listTheory.SNOC,word_bits_n2w,w2w_n2w,BITS_THM,
    WORD_ADD_0,REG_WRITE_INC_PC,REG_READ_WRITE,REG_READ_INC_PC,UP_DOWN_ZERO,
    TRANSFER_LDM,TRANSFER_LDM2,TRANSFER_STM,LDM_LIST_def,
    cond_pass_enc_ldm_stm,decode_enc_ldm_stm,decode_ldm_stm_enc];

val ARM_LDM = SYMBOLIC_EVAL_CONV LDM_STM_ss (cntxt
  [``Abbrev (l = REGISTER_LIST list)``]
  ``enc (instruction$LDM c <| Pre := F; Up := T; BSN := F; Wb := F |>
         Rd list)``);

val ARM_STM = SYMBOLIC_EVAL_CONV LDM_STM_ss (cntxt
  [``Abbrev (l = REGISTER_LIST list)``]
  ``enc (instruction$STM c <| Pre := F; Up := T; BSN := F; Wb := F |>
         Rd list)``);

(* ------------------------------------------------------------------------- *)

val _ = save_thm("ARM_UNDEF", ARM_UNDEF);

val _ = save_thm("ARM_B_NOP",   ARM_B_NOP);
val _ = save_thm("ARM_BL_NOP",  ARM_BL_NOP);
val _ = save_thm("ARM_SWI_NOP", ARM_SWI_NOP);
val _ = save_thm("ARM_AND_NOP", ARM_AND_NOP);
val _ = save_thm("ARM_EOR_NOP", ARM_EOR_NOP);
val _ = save_thm("ARM_SUB_NOP", ARM_SUB_NOP);
val _ = save_thm("ARM_RSB_NOP", ARM_RSB_NOP);
val _ = save_thm("ARM_ADD_NOP", ARM_ADD_NOP);
val _ = save_thm("ARM_ADC_NOP", ARM_ADC_NOP);
val _ = save_thm("ARM_SBC_NOP", ARM_SBC_NOP);
val _ = save_thm("ARM_RSC_NOP", ARM_RSC_NOP);
val _ = save_thm("ARM_TST_NOP", ARM_TST_NOP);
val _ = save_thm("ARM_TEQ_NOP", ARM_TEQ_NOP);
val _ = save_thm("ARM_CMP_NOP", ARM_CMP_NOP);
val _ = save_thm("ARM_CMN_NOP", ARM_CMN_NOP);
val _ = save_thm("ARM_ORR_NOP", ARM_ORR_NOP);
val _ = save_thm("ARM_MOV_NOP", ARM_MOV_NOP);
val _ = save_thm("ARM_BIC_NOP", ARM_BIC_NOP);
val _ = save_thm("ARM_MVN_NOP", ARM_MVN_NOP);
val _ = save_thm("ARM_MUL_NOP", ARM_MUL_NOP);
val _ = save_thm("ARM_MLA_NOP", ARM_MLA_NOP);
val _ = save_thm("ARM_LDR_NOP", ARM_LDR_NOP);
val _ = save_thm("ARM_STR_NOP", ARM_STR_NOP);
val _ = save_thm("ARM_LDM_NOP", ARM_LDM_NOP);
val _ = save_thm("ARM_STM_NOP", ARM_STM_NOP);
val _ = save_thm("ARM_SWP_NOP", ARM_SWP_NOP);
val _ = save_thm("ARM_UND_NOP", ARM_UND_NOP);

val _ = save_thm("ARM_B",   ARM_B);
val _ = save_thm("ARM_BL",  ARM_BL);
val _ = save_thm("ARM_SWI", ARM_SWI);
val _ = save_thm("ARM_UND", ARM_UND);

val _ = save_thm("ARM_TST", ARM_TST);
val _ = save_thm("ARM_TEQ", ARM_TEQ);
val _ = save_thm("ARM_CMP", ARM_CMP);
val _ = save_thm("ARM_CMN", ARM_CMN);

(*
val _ = save_thm("ARM_TST_LSL", ARM_TST_LSL);
val _ = save_thm("ARM_TEQ_LSL", ARM_TEQ_LSL);
val _ = save_thm("ARM_CMP_LSL", ARM_CMP_LSL);
val _ = save_thm("ARM_CMN_LSL", ARM_CMN_LSL);
val _ = save_thm("ARM_TST_LSR", ARM_TST_LSR);
val _ = save_thm("ARM_TEQ_LSR", ARM_TEQ_LSR);
val _ = save_thm("ARM_CMP_LSR", ARM_CMP_LSR);
val _ = save_thm("ARM_CMN_LSR", ARM_CMN_LSR);
*)

val _ = save_thm("ARM_AND", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_AND);
val _ = save_thm("ARM_EOR", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_EOR);
val _ = save_thm("ARM_SUB", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SUB);
val _ = save_thm("ARM_RSB", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSB);
val _ = save_thm("ARM_ADD", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADD);
val _ = save_thm("ARM_ORR", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ORR);
val _ = save_thm("ARM_MOV", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MOV);
val _ = save_thm("ARM_BIC", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_BIC);
val _ = save_thm("ARM_MVN", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MVN);

val _ = save_thm("ARM_AND_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_AND_LSL);
val _ = save_thm("ARM_EOR_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_EOR_LSL);
val _ = save_thm("ARM_SUB_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SUB_LSL);
val _ = save_thm("ARM_RSB_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSB_LSL);
val _ = save_thm("ARM_ADD_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADD_LSL);
val _ = save_thm("ARM_ORR_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ORR_LSL);
val _ = save_thm("ARM_MOV_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MOV_LSL);
val _ = save_thm("ARM_BIC_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_BIC_LSL);
val _ = save_thm("ARM_MVN_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MVN_LSL);

val _ = save_thm("ARM_AND_LSR", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_AND_LSR);
val _ = save_thm("ARM_EOR_LSR", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_EOR_LSR);
val _ = save_thm("ARM_SUB_LSR", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SUB_LSR);
val _ = save_thm("ARM_RSB_LSR", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSB_LSR);
val _ = save_thm("ARM_ADD_LSR", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADD_LSR);
val _ = save_thm("ARM_ORR_LSR", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ORR_LSR);
val _ = save_thm("ARM_MOV_LSR", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MOV_LSR);
val _ = save_thm("ARM_BIC_LSR", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_BIC_LSR);
val _ = save_thm("ARM_MVN_LSR", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MVN_LSR);

val _ = save_thm("ARM_AND_PC", SPEC_TO_PC ARM_AND);
val _ = save_thm("ARM_EOR_PC", SPEC_TO_PC ARM_EOR);
val _ = save_thm("ARM_SUB_PC", SPEC_TO_PC ARM_SUB);
val _ = save_thm("ARM_RSB_PC", SPEC_TO_PC ARM_RSB);
val _ = save_thm("ARM_ADD_PC", SPEC_TO_PC ARM_ADD);
val _ = save_thm("ARM_ORR_PC", SPEC_TO_PC ARM_ORR);
val _ = save_thm("ARM_MOV_PC", SPEC_TO_PC ARM_MOV);
val _ = save_thm("ARM_BIC_PC", SPEC_TO_PC ARM_BIC);
val _ = save_thm("ARM_MVN_PC", SPEC_TO_PC ARM_MVN);

val _ = save_thm("ARM_AND_LSL_PC", SPEC_TO_PC ARM_AND_LSL);
val _ = save_thm("ARM_EOR_LSL_PC", SPEC_TO_PC ARM_EOR_LSL);
val _ = save_thm("ARM_SUB_LSL_PC", SPEC_TO_PC ARM_SUB_LSL);
val _ = save_thm("ARM_RSB_LSL_PC", SPEC_TO_PC ARM_RSB_LSL);
val _ = save_thm("ARM_ADD_LSL_PC", SPEC_TO_PC ARM_ADD_LSL);
val _ = save_thm("ARM_ORR_LSL_PC", SPEC_TO_PC ARM_ORR_LSL);
val _ = save_thm("ARM_MOV_LSL_PC", SPEC_TO_PC ARM_MOV_LSL);
val _ = save_thm("ARM_BIC_LSL_PC", SPEC_TO_PC ARM_BIC_LSL);
val _ = save_thm("ARM_MVN_LSL_PC", SPEC_TO_PC ARM_MVN_LSL);

val _ = save_thm("ARM_AND_LSR_PC", SPEC_TO_PC ARM_AND_LSR);
val _ = save_thm("ARM_EOR_LSR_PC", SPEC_TO_PC ARM_EOR_LSR);
val _ = save_thm("ARM_SUB_LSR_PC", SPEC_TO_PC ARM_SUB_LSR);
val _ = save_thm("ARM_RSB_LSR_PC", SPEC_TO_PC ARM_RSB_LSR);
val _ = save_thm("ARM_ADD_LSR_PC", SPEC_TO_PC ARM_ADD_LSR);
val _ = save_thm("ARM_ORR_LSR_PC", SPEC_TO_PC ARM_ORR_LSR);
val _ = save_thm("ARM_MOV_LSR_PC", SPEC_TO_PC ARM_MOV_LSR);
val _ = save_thm("ARM_BIC_LSR_PC", SPEC_TO_PC ARM_BIC_LSR);
val _ = save_thm("ARM_MVN_LSR_PC", SPEC_TO_PC ARM_MVN_LSR);

val _ = save_thm("ARM_ANDS", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ANDS);
val _ = save_thm("ARM_EORS", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_EORS);
val _ = save_thm("ARM_SUBS", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SUBS);
val _ = save_thm("ARM_RSBS", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSBS);
val _ = save_thm("ARM_ADDS", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADDS);
val _ = save_thm("ARM_ORRS", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ORRS);
val _ = save_thm("ARM_MOVS", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MOVS);
val _ = save_thm("ARM_BICS", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_BICS);
val _ = save_thm("ARM_MVNS", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MVNS);

val _ = save_thm("ARM_ANDS_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_AND_LSL);
val _ = save_thm("ARM_EORS_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_EOR_LSL);
val _ = save_thm("ARM_SUBS_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SUB_LSL);
val _ = save_thm("ARM_RSBS_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSB_LSL);
val _ = save_thm("ARM_ADDS_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADD_LSL);
val _ = save_thm("ARM_ORRS_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ORR_LSL);
val _ = save_thm("ARM_MOVS_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MOV_LSL);
val _ = save_thm("ARM_BICS_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_BIC_LSL);
val _ = save_thm("ARM_MVNS_LSL", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MVN_LSL);

val _ = save_thm("ARM_ANDS_LSR",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ANDS_LSR);
val _ = save_thm("ARM_EORS_LSR",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_EORS_LSR);
val _ = save_thm("ARM_SUBS_LSR",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SUBS_LSR);
val _ = save_thm("ARM_RSBS_LSR",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSBS_LSR);
val _ = save_thm("ARM_ADDS_LSR",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADDS_LSR);
val _ = save_thm("ARM_ORRS_LSR",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ORRS_LSR);
val _ = save_thm("ARM_MOVS_LSR",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MOVS_LSR);
val _ = save_thm("ARM_BICS_LSR",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_BICS_LSR);
val _ = save_thm("ARM_MVNS_LSR",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MVNS_LSR);

val _ = save_thm("ARM_ANDS_PC", SPEC_TO_PC ARM_ANDS);
val _ = save_thm("ARM_EORS_PC", SPEC_TO_PC ARM_EORS);
val _ = save_thm("ARM_SUBS_PC", SPEC_TO_PC ARM_SUBS);
val _ = save_thm("ARM_RSBS_PC", SPEC_TO_PC ARM_RSBS);
val _ = save_thm("ARM_ADDS_PC", SPEC_TO_PC ARM_ADDS);
val _ = save_thm("ARM_ORRS_PC", SPEC_TO_PC ARM_ORRS);
val _ = save_thm("ARM_MOVS_PC", SPEC_TO_PC ARM_MOVS);
val _ = save_thm("ARM_BICS_PC", SPEC_TO_PC ARM_BICS);
val _ = save_thm("ARM_MVNS_PC", SPEC_TO_PC ARM_MVNS);

val _ = save_thm("ARM_ANDS_LSL_PC", SPEC_TO_PC ARM_ANDS_LSL);
val _ = save_thm("ARM_EORS_LSL_PC", SPEC_TO_PC ARM_EORS_LSL);
val _ = save_thm("ARM_SUBS_LSL_PC", SPEC_TO_PC ARM_SUBS_LSL);
val _ = save_thm("ARM_RSBS_LSL_PC", SPEC_TO_PC ARM_RSBS_LSL);
val _ = save_thm("ARM_ADDS_LSL_PC", SPEC_TO_PC ARM_ADDS_LSL);
val _ = save_thm("ARM_ORRS_LSL_PC", SPEC_TO_PC ARM_ORRS_LSL);
val _ = save_thm("ARM_MOVS_LSL_PC", SPEC_TO_PC ARM_MOVS_LSL);
val _ = save_thm("ARM_BICS_LSL_PC", SPEC_TO_PC ARM_BICS_LSL);
val _ = save_thm("ARM_MVNS_LSL_PC", SPEC_TO_PC ARM_MVNS_LSL);

val _ = save_thm("ARM_ANDS_LSR_PC", SPEC_TO_PC ARM_ANDS_LSR);
val _ = save_thm("ARM_EORS_LSR_PC", SPEC_TO_PC ARM_EORS_LSR);
val _ = save_thm("ARM_SUBS_LSR_PC", SPEC_TO_PC ARM_SUBS_LSR);
val _ = save_thm("ARM_RSBS_LSR_PC", SPEC_TO_PC ARM_RSBS_LSR);
val _ = save_thm("ARM_ADDS_LSR_PC", SPEC_TO_PC ARM_ADDS_LSR);
val _ = save_thm("ARM_ORRS_LSR_PC", SPEC_TO_PC ARM_ORRS_LSR);
val _ = save_thm("ARM_MOVS_LSR_PC", SPEC_TO_PC ARM_MOVS_LSR);
val _ = save_thm("ARM_BICS_LSR_PC", SPEC_TO_PC ARM_BICS_LSR);
val _ = save_thm("ARM_MVNS_LSR_PC", SPEC_TO_PC ARM_MVNS_LSR);

val _ = save_thm("ARM_ADCS_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADCS_CARRY);
val _ = save_thm("ARM_SBCS_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SBCS_CARRY);
val _ = save_thm("ARM_RSCS_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSCS_CARRY);
val _ = save_thm("ARM_ADCS_NO_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADCS_NO_CARRY);
val _ = save_thm("ARM_SBCS_NO_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SBCS_NO_CARRY);
val _ = save_thm("ARM_RSCS_NO_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSCS_NO_CARRY);

val _ = save_thm("ARM_ADCS_CARRY_PC", SPEC_TO_PC ARM_ADCS_CARRY);
val _ = save_thm("ARM_SBCS_CARRY_PC", SPEC_TO_PC ARM_SBCS_CARRY);
val _ = save_thm("ARM_RSCS_CARRY_PC", SPEC_TO_PC ARM_RSCS_CARRY);
val _ = save_thm("ARM_ADCS_NO_CARRY_PC", SPEC_TO_PC ARM_ADCS_NO_CARRY);
val _ = save_thm("ARM_SBCS_NO_CARRY_PC", SPEC_TO_PC ARM_SBCS_NO_CARRY);
val _ = save_thm("ARM_RSCS_NO_CARRY_PC", SPEC_TO_PC ARM_RSCS_NO_CARRY);

val _ = save_thm("ARM_ADCS_LSL_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADCS_LSL_CARRY);
val _ = save_thm("ARM_SBCS_LSL_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SBCS_LSL_CARRY);
val _ = save_thm("ARM_RSCS_LSL_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSCS_LSL_CARRY);
val _ = save_thm("ARM_ADCS_LSL_NO_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADCS_LSL_NO_CARRY);
val _ = save_thm("ARM_SBCS_LSL_NO_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SBCS_LSL_NO_CARRY);
val _ = save_thm("ARM_RSCS_LSL_NO_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSCS_LSL_NO_CARRY);

val _ = save_thm("ARM_ADCS_LSL_CARRY_PC", SPEC_TO_PC ARM_ADCS_LSL_CARRY);
val _ = save_thm("ARM_SBCS_LSL_CARRY_PC", SPEC_TO_PC ARM_SBCS_LSL_CARRY);
val _ = save_thm("ARM_RSCS_LSL_CARRY_PC", SPEC_TO_PC ARM_RSCS_LSL_CARRY);
val _ = save_thm("ARM_ADCS_LSL_NO_CARRY_PC", SPEC_TO_PC ARM_ADCS_LSL_NO_CARRY);
val _ = save_thm("ARM_SBCS_LSL_NO_CARRY_PC", SPEC_TO_PC ARM_SBCS_LSL_NO_CARRY);
val _ = save_thm("ARM_RSCS_LSL_NO_CARRY_PC", SPEC_TO_PC ARM_RSCS_LSL_NO_CARRY);

val _ = save_thm("ARM_ADCS_LSR_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADCS_LSR_CARRY);
val _ = save_thm("ARM_SBCS_LSR_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SBCS_LSR_CARRY);
val _ = save_thm("ARM_RSCS_LSR_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSCS_LSR_CARRY);
val _ = save_thm("ARM_ADCS_LSR_NO_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADCS_LSR_NO_CARRY);
val _ = save_thm("ARM_SBCS_LSR_NO_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SBCS_LSR_NO_CARRY);
val _ = save_thm("ARM_RSCS_LSR_NO_CARRY",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSCS_LSR_NO_CARRY);

val _ = save_thm("ARM_ADCS_LSR_CARRY_PC", SPEC_TO_PC ARM_ADCS_LSR_CARRY);
val _ = save_thm("ARM_SBCS_LSR_CARRY_PC", SPEC_TO_PC ARM_SBCS_LSR_CARRY);
val _ = save_thm("ARM_RSCS_LSR_CARRY_PC", SPEC_TO_PC ARM_RSCS_LSR_CARRY);
val _ = save_thm("ARM_ADCS_LSR_NO_CARRY_PC", SPEC_TO_PC ARM_ADCS_LSR_NO_CARRY);
val _ = save_thm("ARM_SBCS_LSR_NO_CARRY_PC", SPEC_TO_PC ARM_SBCS_LSR_NO_CARRY);
val _ = save_thm("ARM_RSCS_LSR_NO_CARRY_PC", SPEC_TO_PC ARM_RSCS_LSR_NO_CARRY);

val _ = save_thm("ARM_MUL", ARM_MUL);
val _ = save_thm("ARM_MLA", ARM_MLA);
val _ = save_thm("ARM_MULS", ARM_MULS);
val _ = save_thm("ARM_MLAS", ARM_MLAS);

val _ = save_thm("ARM_LDR", ARM_LDR);
val _ = save_thm("ARM_STR", ARM_STR);
val _ = save_thm("ARM_LDM", ARM_LDM);
val _ = save_thm("ARM_STM", ARM_STM);
val _ = save_thm("ARM_SWP", ARM_SWP);

val _ = save_thm("ARM_LDR_BYTE", ARM_LDR_BYTE);
val _ = save_thm("ARM_STR_BYTE", ARM_STR_BYTE);
val _ = save_thm("ARM_SWP_BYTE", ARM_SWP_BYTE);

val _ = save_thm("ARM_LDR_POST_UP_IMM", ARM_LDR_POST_UP_IMM);
val _ = save_thm("ARM_LDR_POST_UP_REG", ARM_LDR_POST_UP_REG);
val _ = save_thm("ARM_LDR_POST_UP_LSL_REG", ARM_LDR_POST_UP_LSL_REG);
val _ = save_thm("ARM_STR_POST_UP_IMM", ARM_STR_POST_UP_IMM);
val _ = save_thm("ARM_STR_POST_UP_REG", ARM_STR_POST_UP_REG);
val _ = save_thm("ARM_STR_POST_UP_LSL_REG", ARM_STR_POST_UP_LSL_REG);
val _ = save_thm("ARM_LDR_PRE_UP_WB_IMM", ARM_LDR_PRE_UP_WB_IMM);
val _ = save_thm("ARM_LDR_PRE_UP_WB_REG", ARM_LDR_PRE_UP_WB_REG);
val _ = save_thm("ARM_LDR_PRE_UP_WB_LSL_REG", ARM_LDR_PRE_UP_WB_LSL_REG);
val _ = save_thm("ARM_STR_PRE_UP_WB_IMM", ARM_STR_PRE_UP_WB_IMM);
val _ = save_thm("ARM_STR_PRE_UP_WB_REG", ARM_STR_PRE_UP_WB_REG);
val _ = save_thm("ARM_STR_PRE_UP_WB_LSL_REG", ARM_STR_PRE_UP_WB_LSL_REG);
val _ = save_thm("ARM_LDR_BYTE_POST_UP_IMM", ARM_LDR_BYTE_POST_UP_IMM);
val _ = save_thm("ARM_LDR_BYTE_POST_UP_REG", ARM_LDR_BYTE_POST_UP_REG);
val _ = save_thm("ARM_LDR_BYTE_POST_UP_LSL_REG", ARM_LDR_BYTE_POST_UP_LSL_REG);
val _ = save_thm("ARM_STR_BYTE_POST_UP_IMM", ARM_STR_BYTE_POST_UP_IMM);
val _ = save_thm("ARM_STR_BYTE_POST_UP_REG", ARM_STR_BYTE_POST_UP_REG);
val _ = save_thm("ARM_STR_BYTE_POST_UP_LSL_REG", ARM_STR_BYTE_POST_UP_LSL_REG);
val _ = save_thm("ARM_LDR_BYTE_PRE_UP_WB_IMM", ARM_LDR_BYTE_PRE_UP_WB_IMM);
val _ = save_thm("ARM_LDR_BYTE_PRE_UP_WB_REG", ARM_LDR_BYTE_PRE_UP_WB_REG);
val _ = save_thm("ARM_LDR_BYTE_PRE_UP_WB_LSL_REG",
  ARM_LDR_BYTE_PRE_UP_WB_LSL_REG);
val _ = save_thm("ARM_STR_BYTE_PRE_UP_WB_IMM", ARM_STR_BYTE_PRE_UP_WB_IMM);
val _ = save_thm("ARM_STR_BYTE_PRE_UP_WB_REG", ARM_STR_BYTE_PRE_UP_WB_REG);
val _ = save_thm("ARM_STR_BYTE_PRE_UP_WB_LSL_REG",
  ARM_STR_BYTE_PRE_UP_WB_LSL_REG);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
