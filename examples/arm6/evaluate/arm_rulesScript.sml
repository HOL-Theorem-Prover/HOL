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

fun UNABBREVL_RULE l t =
   GEN_ALL (foldl (fn (x,t) => armLib.UNABBREV_RULE x t) (SPEC_ALL t) l);

(* ------------------------------------------------------------------------- *)

val SPSR_WRITE_THM = store_thm("SPSR_WRITE_THM",
  `!psr m x. USER m ==> (SPSR_WRITE psr m x = psr)`,
  SIMP_TAC std_ss [SPSR_WRITE_def]);

val SPSR_WRITE_WRITE = store_thm("SPSR_WRITE_WRITE",
  `!psr m x y. SPSR_WRITE (SPSR_WRITE psr m x) m y = SPSR_WRITE psr m y`,
  RW_TAC std_ss [SPSR_WRITE_def,SUBST_EQ]);

val SPSR_WRITE_READ = store_thm("SPSR_WRITE_READ",
  `!psr m x. ~USER m ==> (SPSR_READ (SPSR_WRITE psr m x) m = x) /\
                         (SPSR_READ (CPSR_WRITE psr x) m = SPSR_READ psr m)`,
  RW_TAC std_ss [SPSR_WRITE_def,CPSR_WRITE_def,SPSR_READ_def,SUBST_def]
    \\ Cases_on `m` \\ FULL_SIMP_TAC (srw_ss()) [USER_def,mode2psr_def]);

(* ------------------------------------------------------------------------- *)

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

val REG_WRITE_READ =
  (GEN_ALL o SIMP_RULE std_ss [REG_READ_READ6] o
   DISCH `~(n2 = 15w)` o SPEC_ALL o CONJUNCT1) lemmasTheory.REG_READ_WRITE;

val INC_PC = save_thm("INC_PC",
  (SIMP_RULE std_ss [coreTheory.REG_READ6_def,FETCH_PC_def] o
   hd o tl o CONJUNCTS) TO_WRITE_READ6);

val REG_WRITEL_def = Define`
  (REG_WRITEL r m [] = r) /\
  (REG_WRITEL r m ((n,d)::l) = REG_WRITE (REG_WRITEL r m l) m n d)`;

val REG_WRITEL = store_thm("REG_WRITEL",
  `!r m l. REG_WRITEL r m l = FOLDR (\h r. REG_WRITE r m (FST h) (SND h)) r l`,
  Induct_on `l` \\ TRY (Cases_on `h`) \\ ASM_SIMP_TAC list_ss [REG_WRITEL_def]);

val REG_WRITE_WRITEL = store_thm("REG_WRITE_WRITEL",
  `!r m n d. REG_WRITE r m n d = REG_WRITEL r m [(n,d)]`,
  SIMP_TAC std_ss [REG_WRITEL_def]);

val REG_WRITEL_WRITEL = store_thm("REG_WRITEL_WRITEL",
  `!r m l1 l2. REG_WRITEL (REG_WRITEL r m l1) m l2 = REG_WRITEL r m (l2 ++ l1)`,
  SIMP_TAC std_ss [REG_WRITEL,rich_listTheory.FOLDR_APPEND]);

val REG_WRITE_WRITE_THM = store_thm("REG_WRITE_WRITE_THM",
  `!m n r m e d. x <=+ y ==>
      (REG_WRITE (REG_WRITE r m x e) m y d =
         if x = y then
           REG_WRITE r m y d
         else
           REG_WRITE (REG_WRITE r m y d) m x e)`,
  RW_TAC std_ss [WORD_LOWER_OR_EQ,WORD_LO,REG_WRITE_WRITE]
    \\ METIS_TAC [REG_WRITE_def,not_reg_eq,SUBST_NE_COMMUTES,
         mode_reg2num_lt,num2register_11]);

val REG_READ_WRITEL = store_thm("REG_READ_WRITEL",
  `(!r m n. REG_READ (REG_WRITEL r m []) m n = REG_READ r m n) /\
   (!r m n a b l. ~(n = 15w) ==>
      (REG_READ (REG_WRITEL r m ((a,b)::l)) m n =
       if a = n then b else REG_READ (REG_WRITEL r m l) m n))`,
  RW_TAC std_ss [REG_WRITEL_def,REG_WRITE_READ]);

val mode_reg2num_15 = (GEN_ALL o SIMP_RULE (arith_ss++SIZES_ss) [w2n_n2w] o
  SPECL [`m`,`15w`]) mode_reg2num_def;

val lem = (SIMP_RULE std_ss[lemmasTheory.REG_READ_WRITE_PC,
  TO_WRITE_READ6,WORD_ADD_SUB] o SPECL [`r`,`m`,`15w`,`d + 8w`]) READ_TO_READ6;

val lem2 = prove(
  `!r m m2 n d. ~(n = 15w) ==>
     (REG_READ (REG_WRITE r m n d) m2 15w = REG_READ r m2 15w)`,
  RW_TAC std_ss [REG_READ_def,REG_WRITE_def,SUBST_def,
         r15,mode_reg2num_lt,num2register_11]
    \\ METIS_TAC [mode_reg2num_15,not_reg_eq]);

val REG_READ_WRITEL_PC = store_thm("REG_READ_WRITEL_PC",
  `!r m m2 a b l. REG_READ (REG_WRITEL r m ((a,b)::l)) m2 15w =
       if a = 15w then b + 8w else REG_READ (REG_WRITEL r m l) m2 15w`,
  RW_TAC std_ss [REG_WRITEL_def,TO_WRITE_READ6,lem,lem2]);

val REG_READ_WRITEL_PC2 = store_thm("REG_READ_WRITEL_PC2",
  `!r m a b l. (REG_WRITEL r m ((a,b)::l)) r15 =
       if a = 15w then b else (REG_WRITEL r m l) r15`,
  RW_TAC std_ss [REG_WRITEL_def,REG_WRITE_def,SUBST_def,
         r15,mode_reg2num_lt,num2register_11]
    \\ METIS_TAC [mode_reg2num_15,not_reg_eq]);

(* ------------------------------------------------------------------------- *)

val MOD_0 = (GSYM o REWRITE_RULE [ZERO_LT_TOP] o SPEC `TOP (:i32)`) ZERO_MOD;

val MOD_2EXP_32 =
  simpLib.SIMP_PROVE (std_ss++wordsLib.SIZES_ss) [MOD_2EXP_def,TOP_def]
  ``MOD_2EXP 32 n = n MOD TOP (:i32)``;

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

val lem = prove(`!a b c. ADD a b c = if c then ADD a b T else ADD a b F`,
  RW_TAC bool_ss []);

val ALU_ADD = SIMP_RULE std_ss [ALU_ADD_NO_CARRY,ALU_ADD_CARRY] lem;

(* ......................................................................... *)

val n2w_2EXP_32 = (EQT_ELIM o EVAL) ``n2w (TOP (:i32)) = 0w:word32``;

val n2w_sub1 = EVAL ``n2w (TOP (:i32) - 1 MOD TOP (:i32))``;

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

val lem = prove(`!a b c. SUB a b c = if c then SUB a b T else SUB a b F`,
  RW_TAC bool_ss []);

val ALU_SUB = SIMP_RULE std_ss [ALU_SUB_NO_CARRY,ALU_SUB_CARRY] lem;

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
  ``!i n. i < dimindex (:'a) ==> ((n2w n):bool ** 'a %% i = BIT i n)``;

val CARRY_NZCV = METIS_PROVE [CARRY_def,NZCV_def] ``CARRY (NZCV x) = x %% 29``;

fun DISCH_AND_IMP t =
  (GEN_ALL o SIMP_RULE (srw_ss()) [REG_WRITE_INC_PC,AND_IMP_INTRO] o
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
  cond_pass_enc_ldr_str,cond_pass_enc_ldm_stm,cond_pass_enc_swp,
  cond_pass_enc_mrs,cond_pass_enc_msr];

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

val ARM_MRS_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$MRS c r Rd)``);

val ARM_MSR_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$MSR c psrd op2)``);

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
  rewrites [DATA_PROCESSING_def,ARITHMETIC_def,TEST_OR_COMP_def,ALU_def,
   ALU_ADD,ALU_SUB,LSL_def,LSR_def,AND_def,ORR_def,EOR_def,ALU_logic_def,
   SET_NZC_def,ADDR_MODE1_def,LSL_NOT_ZERO,WORD_NEG_cor,WORD_1COMP_ZERO,SND_ROR,
   cond_pass_enc_data_proc, decode_enc_data_proc, decode_data_proc_enc,
   cond_pass_enc_data_proc2,decode_enc_data_proc2,decode_data_proc_enc2,
   cond_pass_enc_data_proc3,decode_enc_data_proc3,decode_data_proc_enc3,
   immediate_enc,shift_immediate_enc,shift_immediate_shift_register];

(* ......................................................................... *)

val PAIR_RULE =
  SIMP_RULE (srw_ss()) [FST_COND_RAND,SND_COND_RAND] o PairRules.PBETA_RULE;

val abbrev_imm =
 ``Abbrev (n:word32 = w2w (imm:word8) #>> w2n (2w:word8 * w2w (rot:word4)))``;

fun eval_op t = SYMBOLIC_EVAL_CONV DP_ss (cntxt [abbrev_imm]
  (subst [``f:condition -> bool -> bool ** i4 ->
              bool ** i4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``enc ((f:condition -> bool -> bool ** i4 ->
             bool ** i4 -> addr_mode1 -> arm_instruction)
       c F Rd Rm (Dp_immediate rot imm))``));

val thms = map eval_op
   [``instruction$AND``,``instruction$EOR``,``instruction$SUB``,
    ``instruction$RSB``,``instruction$ADD``,``instruction$ORR``,
    ``instruction$BIC``];

val (ARM_AND_IMM,thms) = hd_tl thms;
val (ARM_EOR_IMM,thms) = hd_tl thms;
val (ARM_SUB_IMM,thms) = hd_tl thms;
val (ARM_RSB_IMM,thms) = hd_tl thms;
val (ARM_ADD_IMM,thms) = hd_tl thms;
val (ARM_ORR_IMM,thms) = hd_tl thms;
val ARM_BIC_IMM = hd thms;

val thms = map (PAIR_RULE o eval_op)
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``];

val (ARM_ADC_IMM,thms) = hd_tl thms;
val (ARM_SBC_IMM,thms) = hd_tl thms;
val ARM_RSC_IMM = hd thms;

fun eval_op t = SYMBOLIC_EVAL_CONV DP_ss (cntxt
  [``Abbrev (n:word32 = w2w (imm:word8) #>> w2n (2w:word8 * w2w (rot:word4)))``]
  (subst [``f:condition -> bool -> bool ** i4 ->
              bool ** i4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``enc ((f:condition -> bool -> bool ** i4 ->
             bool ** i4 -> addr_mode1 -> arm_instruction)
       c T Rd Rm (Dp_immediate rot imm))``));

val thms = map eval_op
   [``instruction$AND``,``instruction$EOR``,``instruction$SUB``,
    ``instruction$RSB``,``instruction$ADD``,``instruction$ORR``,
    ``instruction$BIC``];

val (ARM_ANDS_IMM,thms) = hd_tl thms;
val (ARM_EORS_IMM,thms) = hd_tl thms;
val (ARM_SUBS_IMM,thms) = hd_tl thms;
val (ARM_RSBS_IMM,thms) = hd_tl thms;
val (ARM_ADDS_IMM,thms) = hd_tl thms;
val (ARM_ORRS_IMM,thms) = hd_tl thms;
val ARM_BICS_IMM = hd thms;

val thms = map (PAIR_RULE o eval_op)
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``];

val (ARM_ADCS_IMM,thms) = hd_tl thms;
val (ARM_SBCS_IMM,thms) = hd_tl thms;
val ARM_RSCS_IMM = hd thms;

(* ......................................................................... *)

fun eval_op t = SYMBOLIC_EVAL_CONV DP_ss (cntxt []
  (subst [``f:condition -> bool -> bool ** i4 ->
              bool ** i4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``enc ((f:condition -> bool -> bool ** i4 ->
             bool ** i4 -> addr_mode1 -> arm_instruction)
       c F Rd Rm (Dp_shift_immediate (LSL Rn) 0w))``));

val thms = map eval_op
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

val thms = map (PAIR_RULE o eval_op)
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``];

val (ARM_ADC,thms) = hd_tl thms;
val (ARM_SBC,thms) = hd_tl thms;
val ARM_RSC = hd thms;

fun eval_op t = SYMBOLIC_EVAL_CONV DP_ss (cntxt []
  (subst [``f:condition -> bool -> bool ** i4 ->
              bool ** i4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``enc ((f:condition -> bool -> bool ** i4 ->
             bool ** i4 -> addr_mode1 -> arm_instruction)
       c T Rd Rm (Dp_shift_immediate (LSL Rn) 0w))``));

val thms = map eval_op
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

val thms = map (PAIR_RULE o eval_op)
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``];

val (ARM_ADCS,thms) = hd_tl thms;
val (ARM_SBCS,thms) = hd_tl thms;
val ARM_RSCS = hd thms;

(* ......................................................................... *)

fun eval_op t = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  (subst [``f:condition -> bool -> bool ** i4 ->
              bool ** i4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``enc ((f:condition -> bool -> bool ** i4 ->
             bool ** i4 -> addr_mode1 -> arm_instruction)
       c F Rd Rm (Dp_shift_immediate (LSL Rn) n))``));

val thms = map eval_op
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

val thms = map (PAIR_RULE o eval_op)
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``];

val (ARM_ADC_LSL,thms) = hd_tl thms;
val (ARM_SBC_LSL,thms) = hd_tl thms;
val ARM_RSC_LSL = hd thms;

fun eval_op t = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  (subst [``f:condition -> bool -> bool ** i4 ->
              bool ** i4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``enc ((f:condition -> bool -> bool ** i4 ->
             bool ** i4 -> addr_mode1 -> arm_instruction)
       c T Rd Rm (Dp_shift_immediate (LSL Rn) n))``));

val thms = map eval_op
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

val thms = map (PAIR_RULE o eval_op)
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``];

val (ARM_ADCS_LSL,thms) = hd_tl thms;
val (ARM_SBCS_LSL,thms) = hd_tl thms;
val ARM_RSCS_LSL = hd thms;

(* ......................................................................... *)

fun eval_op t = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  (subst [``f:condition -> bool -> bool ** i4 ->
              bool ** i4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``enc ((f:condition -> bool -> bool ** i4 ->
             bool ** i4 -> addr_mode1 -> arm_instruction)
       c F Rd Rm (Dp_shift_immediate (LSR Rn) n))``));

val thms = map eval_op
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

val thms = map (PAIR_RULE o eval_op)
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``];

val (ARM_ADC_LSR,thms) = hd_tl thms;
val (ARM_SBC_LSR,thms) = hd_tl thms;
val ARM_RSC_LSR = hd thms;

fun eval_op t = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  (subst [``f:condition -> bool -> bool ** i4 ->
              bool ** i4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``enc ((f:condition -> bool -> bool ** i4 ->
             bool ** i4 -> addr_mode1 -> arm_instruction)
       c T Rd Rm (Dp_shift_immediate (LSR Rn) n))``));

val thms = map eval_op
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

val thms = map (PAIR_RULE o eval_op)
   [``instruction$ADC``,``instruction$SBC``,``instruction$RSC``];

val (ARM_ADCS_LSR,thms) = hd_tl thms;
val (ARM_SBCS_LSR,thms) = hd_tl thms;
val ARM_RSCS_LSR = hd thms;

(* ......................................................................... *)

val ARM_MOV = SYMBOLIC_EVAL_CONV DP_ss (cntxt []
  ``enc (instruction$MOV c F Rd (Dp_shift_immediate (LSL Rn) 0w))``);

val ARM_MVN = SYMBOLIC_EVAL_CONV DP_ss (cntxt []
  ``enc (instruction$MVN c F Rd (Dp_shift_immediate (LSL Rn) 0w))``);

val ARM_MOVS = SYMBOLIC_EVAL_CONV DP_ss (cntxt []
  ``enc (instruction$MOV c T Rd (Dp_shift_immediate (LSL Rn) 0w))``);

val ARM_MVNS = SYMBOLIC_EVAL_CONV DP_ss (cntxt []
  ``enc (instruction$MVN c T Rd (Dp_shift_immediate (LSL Rn) 0w))``);

val ARM_MOV_IMM = SYMBOLIC_EVAL_CONV DP_ss (cntxt []
  ``enc (instruction$MOV c F Rd (Dp_immediate rot imm))``);

val ARM_MOV_LSL = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  ``enc (instruction$MOV c F Rd (Dp_shift_immediate (LSL Rn) n))``);

val ARM_MOV_LSR = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  ``enc (instruction$MOV c F Rd (Dp_shift_immediate (LSR Rn) n))``);

val ARM_MVN_IMM = SYMBOLIC_EVAL_CONV DP_ss (cntxt []
  ``enc (instruction$MVN c F Rd (Dp_immediate rot imm))``);

val ARM_MVN_LSL = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  ``enc (instruction$MVN c F Rd (Dp_shift_immediate (LSL Rn) n))``);

val ARM_MVN_LSR = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  ``enc (instruction$MVN c F Rd (Dp_shift_immediate (LSR Rn) n))``);

val ARM_MOVS_IMM = SYMBOLIC_EVAL_CONV DP_ss (cntxt [abbrev_imm]
  ``enc (instruction$MOV c T Rd (Dp_immediate rot imm))``);

val ARM_MOVS_LSL = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  ``enc (instruction$MOV c T Rd (Dp_shift_immediate (LSL Rn) n))``);

val ARM_MOVS_LSR = SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(n = 0w:word5)``]
  ``enc (instruction$MOV c T Rd (Dp_shift_immediate (LSR Rn) n))``);

val ARM_MVNS_IMM = SYMBOLIC_EVAL_CONV DP_ss (cntxt [abbrev_imm]
  ``enc (instruction$MVN c T Rd (Dp_immediate rot imm))``);

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

val ARM_B = UNABBREVL_RULE [`Reg`,`mode`]
  (SYMBOLIC_EVAL_CONV BRANCH_ss (cntxt [] ``enc (instruction$B c offset)``));

val ARM_BL = UNABBREVL_RULE [`Reg`]
  (SYMBOLIC_EVAL_CONV BRANCH_ss (cntxt [] ``enc (instruction$BL c offset)``));

val SWI_EX_ss =
  rewrites [EXCEPTION_def,exception2mode_def,exception2num_thm,
    cond_pass_enc_swi,decode_enc_swi,cond_pass_enc_coproc,decode_enc_coproc];

val ARM_SWI = UNABBREVL_RULE [`Reg`,`mode`]
  (SYMBOLIC_EVAL_CONV SWI_EX_ss (cntxt [] ``enc (instruction$SWI c)``));

val ARM_UND = UNABBREVL_RULE [`Reg`,`mode`]
  (SYMBOLIC_EVAL_CONV SWI_EX_ss (cntxt [] ``enc (instruction$UND c)``));

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

(* ......................................................................... *)

val lem = METIS_PROVE [DECIDE ``!i. ~(28 <= i \/ i <= 7) = 8 <= i /\ i <= 27``]
 ``!rm. (\i b. 28 <= i /\ (rm:word32) %% i \/
                8 <= i /\ i <= 27 /\ b \/ i <= 7 /\ rm %% i) =
   (\i b. if i <= 7 \/ 28 <= i then rm %% i else b)``;

val lem2 = METIS_PROVE [DECIDE ``!i. ~(28 <= i) = 8 <= i /\ i <= 27 \/ i <= 7``]
 ``!rm. (\i b. 28 <= i /\ (rm:word32) %% i \/
                8 <= i /\ i <= 27 /\ b \/ i <= 7 /\ b) =
   (\i b. if 28 <= i then rm %% i else b)``;

val lem3 = SIMP_RULE (std_ss++armLib.PBETA_ss) [] (prove(
  `!op2 c.  let (I,R,bit19,bit16,Rm,opnd) =
              DECODE_MSR (enc (instruction$MSR c SPSR_a op2)) in
     (R \/ (~bit19 /\ bit16)) \/ (~bit19 /\ ~bit16)`,
  Cases \\ SIMP_TAC std_ss [DECODE_PSRD_def,decode_msr_enc]));

val MRS_MSR_ss =
  rewrites [MSR_def,MRS_def,DECODE_PSRD_def,SND_ROR,lem,lem2,lem3,
    immediate_enc,cond_pass_enc_msr,decode_enc_msr,decode_msr_enc,
    cond_pass_enc_mrs,decode_enc_mrs,decode_mrs_enc];

val ARM_MSR_SPSR_USR = UNABBREVL_RULE [`Reg`]
  (SYMBOLIC_EVAL_CONV MRS_MSR_ss (cntxt [``USER mode``]
   ``enc (instruction$MSR c SPSR_a op2)``));

val ARM_MSR_CPSR_USR = SYMBOLIC_EVAL_CONV MRS_MSR_ss (cntxt [``USER mode``]
  ``enc (instruction$MSR c CPSR_a (Msr_register Rm))``);

val ARM_MSR_CPSR_SYS = SYMBOLIC_EVAL_CONV MRS_MSR_ss (cntxt [``~USER mode``]
  ``enc (instruction$MSR c CPSR_a (Msr_register Rm))``);

val ARM_MSR_SPSR_SYS = SYMBOLIC_EVAL_CONV MRS_MSR_ss (cntxt [``~USER mode``]
  ``enc (instruction$MSR c SPSR_a (Msr_register Rm))``);

val ARM_MSR_CPSR_IMM_USR = UNABBREVL_RULE [`Reg`]
  (SYMBOLIC_EVAL_CONV MRS_MSR_ss (cntxt [``USER mode``]
   ``enc (instruction$MSR c CPSR_a (Msr_immediate rot imm))``));

val ARM_MSR_CPSR_IMM_SYS = UNABBREVL_RULE [`Reg`]
  (SYMBOLIC_EVAL_CONV MRS_MSR_ss (cntxt [``~USER mode``]
   ``enc (instruction$MSR c CPSR_a (Msr_immediate rot imm))``));

val ARM_MSR_SPSR_IMM_SYS = UNABBREVL_RULE [`Reg`]
  (SYMBOLIC_EVAL_CONV MRS_MSR_ss (cntxt [``~USER mode``]
   ``enc (instruction$MSR c SPSR_a (Msr_immediate rot imm))``));

val ARM_MRS = UNABBREVL_RULE [`Reg`]
  (SYMBOLIC_EVAL_CONV MRS_MSR_ss (cntxt [] ``enc (instruction$MRS c r Rd)``));

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
val _ = save_thm("ARM_MRS_NOP", ARM_MRS_NOP);
val _ = save_thm("ARM_MSR_NOP", ARM_MSR_NOP);
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

val _ = save_thm("ARM_AND_IMM", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_AND_IMM);
val _ = save_thm("ARM_EOR_IMM", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_EOR_IMM);
val _ = save_thm("ARM_SUB_IMM", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SUB_IMM);
val _ = save_thm("ARM_RSB_IMM", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSB_IMM);
val _ = save_thm("ARM_ADD_IMM", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADD_IMM);
val _ = save_thm("ARM_ORR_IMM", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ORR_IMM);
val _ = save_thm("ARM_MOV_IMM", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MOV_IMM);
val _ = save_thm("ARM_BIC_IMM", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_BIC_IMM);
val _ = save_thm("ARM_MVN_IMM", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MVN_IMM);

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

val _ = save_thm("ARM_AND_IMM_PC", SPEC_TO_PC ARM_AND_IMM);
val _ = save_thm("ARM_EOR_IMM_PC", SPEC_TO_PC ARM_EOR_IMM);
val _ = save_thm("ARM_SUB_IMM_PC", SPEC_TO_PC ARM_SUB_IMM);
val _ = save_thm("ARM_RSB_IMM_PC", SPEC_TO_PC ARM_RSB_IMM);
val _ = save_thm("ARM_ADD_IMM_PC", SPEC_TO_PC ARM_ADD_IMM);
val _ = save_thm("ARM_ORR_IMM_PC", SPEC_TO_PC ARM_ORR_IMM);
val _ = save_thm("ARM_MOV_IMM_PC", SPEC_TO_PC ARM_MOV_IMM);
val _ = save_thm("ARM_BIC_IMM_PC", SPEC_TO_PC ARM_BIC_IMM);
val _ = save_thm("ARM_MVN_IMM_PC", SPEC_TO_PC ARM_MVN_IMM);

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

val _ = save_thm("ARM_ANDS_IMM",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ANDS_IMM);
val _ = save_thm("ARM_EORS_IMM",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_EORS_IMM);
val _ = save_thm("ARM_SUBS_IMM",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SUBS_IMM);
val _ = save_thm("ARM_RSBS_IMM",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSBS_IMM);
val _ = save_thm("ARM_ADDS_IMM",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADDS_IMM);
val _ = save_thm("ARM_ORRS_IMM",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ORRS_IMM);
val _ = save_thm("ARM_MOVS_IMM",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MOVS_IMM);
val _ = save_thm("ARM_BICS_IMM",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_BICS_IMM);
val _ = save_thm("ARM_MVNS_IMM",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MVNS_IMM);

val _ = save_thm("ARM_ANDS_LSL",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ANDS_LSL);
val _ = save_thm("ARM_EORS_LSL",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_EORS_LSL);
val _ = save_thm("ARM_SUBS_LSL",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SUBS_LSL);
val _ = save_thm("ARM_RSBS_LSL",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSBS_LSL);
val _ = save_thm("ARM_ADDS_LSL",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADDS_LSL);
val _ = save_thm("ARM_ORRS_LSL",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ORRS_LSL);
val _ = save_thm("ARM_MOVS_LSL",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MOVS_LSL);
val _ = save_thm("ARM_BICS_LSL",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_BICS_LSL);
val _ = save_thm("ARM_MVNS_LSL",DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MVNS_LSL);

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

val _ = save_thm("ARM_ANDS_IMM_PC", SPEC_TO_PC ARM_ANDS_IMM);
val _ = save_thm("ARM_EORS_IMM_PC", SPEC_TO_PC ARM_EORS_IMM);
val _ = save_thm("ARM_SUBS_IMM_PC", SPEC_TO_PC ARM_SUBS_IMM);
val _ = save_thm("ARM_RSBS_IMM_PC", SPEC_TO_PC ARM_RSBS_IMM);
val _ = save_thm("ARM_ADDS_IMM_PC", SPEC_TO_PC ARM_ADDS_IMM);
val _ = save_thm("ARM_ORRS_IMM_PC", SPEC_TO_PC ARM_ORRS_IMM);
val _ = save_thm("ARM_MOVS_IMM_PC", SPEC_TO_PC ARM_MOVS_IMM);
val _ = save_thm("ARM_BICS_IMM_PC", SPEC_TO_PC ARM_BICS_IMM);
val _ = save_thm("ARM_MVNS_IMM_PC", SPEC_TO_PC ARM_MVNS_IMM);

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

val _ = save_thm("ARM_ADC", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADC);
val _ = save_thm("ARM_SBC", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SBC);
val _ = save_thm("ARM_RSC", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSC);

val _ = save_thm("ARM_ADC_PC", SPEC_TO_PC ARM_ADC);
val _ = save_thm("ARM_SBC_PC", SPEC_TO_PC ARM_SBC);
val _ = save_thm("ARM_RSC_PC", SPEC_TO_PC ARM_RSC);

val _ = save_thm("ARM_ADC_IMM",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADC_IMM);
val _ = save_thm("ARM_SBC_IMM",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SBC_IMM);
val _ = save_thm("ARM_RSC_IMM",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSC_IMM);

val _ = save_thm("ARM_ADC_IMM_PC", SPEC_TO_PC ARM_ADC_IMM);
val _ = save_thm("ARM_SBC_IMM_PC", SPEC_TO_PC ARM_SBC_IMM);
val _ = save_thm("ARM_RSC_IMM_PC", SPEC_TO_PC ARM_RSC_IMM);

val _ = save_thm("ARM_ADC_LSL",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADC_LSL);
val _ = save_thm("ARM_SBC_LSL",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SBC_LSL);
val _ = save_thm("ARM_RSC_LSL",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSC_LSL);

val _ = save_thm("ARM_ADC_LSL_PC", SPEC_TO_PC ARM_ADC_LSL);
val _ = save_thm("ARM_SBC_LSL_PC", SPEC_TO_PC ARM_SBC_LSL);
val _ = save_thm("ARM_RSC_LSL_PC", SPEC_TO_PC ARM_RSC_LSL);

val _ = save_thm("ARM_ADC_LSR",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADC_LSR);
val _ = save_thm("ARM_SBC_LSR",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SBC_LSR);
val _ = save_thm("ARM_RSC_LSR",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSC_LSR);

val _ = save_thm("ARM_ADC_LSR_PC", SPEC_TO_PC ARM_ADC_LSR);
val _ = save_thm("ARM_SBC_LSR_PC", SPEC_TO_PC ARM_SBC_LSR);
val _ = save_thm("ARM_RSC_LSR_PC", SPEC_TO_PC ARM_RSC_LSR);

val _ = save_thm("ARM_ADCS", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADCS);
val _ = save_thm("ARM_SBCS", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SBCS);
val _ = save_thm("ARM_RSCS", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSCS);

val _ = save_thm("ARM_ADCS_PC", SPEC_TO_PC ARM_ADCS);
val _ = save_thm("ARM_SBCS_PC", SPEC_TO_PC ARM_SBCS);
val _ = save_thm("ARM_RSCS_PC", SPEC_TO_PC ARM_RSCS);

val _ = save_thm("ARM_ADCS_IMM",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADCS_IMM);
val _ = save_thm("ARM_SBCS_IMM",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SBCS_IMM);
val _ = save_thm("ARM_RSCS_IMM",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSCS_IMM);

val _ = save_thm("ARM_ADCS_IMM_PC", SPEC_TO_PC ARM_ADCS_IMM);
val _ = save_thm("ARM_SBCS_IMM_PC", SPEC_TO_PC ARM_SBCS_IMM);
val _ = save_thm("ARM_RSCS_IMM_PC", SPEC_TO_PC ARM_RSCS_IMM);

val _ = save_thm("ARM_ADCS_LSL",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADCS_LSL);
val _ = save_thm("ARM_SBCS_LSL",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SBCS_LSL);
val _ = save_thm("ARM_RSCS_LSL",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSCS_LSL);

val _ = save_thm("ARM_ADCS_LSL_PC", SPEC_TO_PC ARM_ADCS_LSL);
val _ = save_thm("ARM_SBCS_LSL_PC", SPEC_TO_PC ARM_SBCS_LSL);
val _ = save_thm("ARM_RSCS_LSL_PC", SPEC_TO_PC ARM_RSCS_LSL);

val _ = save_thm("ARM_ADCS_LSR",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADCS_LSR);
val _ = save_thm("ARM_SBCS_LSR",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SBCS_LSR);
val _ = save_thm("ARM_RSCS_LSR",
  DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSCS_LSR);

val _ = save_thm("ARM_ADCS_LSR_PC", SPEC_TO_PC ARM_ADCS_LSR);
val _ = save_thm("ARM_SBCS_LSR_PC", SPEC_TO_PC ARM_SBCS_LSR);
val _ = save_thm("ARM_RSCS_LSR_PC", SPEC_TO_PC ARM_RSCS_LSR);

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

val _ = save_thm("ARM_MRS",ARM_MRS);

val _ = save_thm("ARM_MSR_CPSR_USR",ARM_MSR_CPSR_USR);
val _ = save_thm("ARM_MSR_CPSR_IMM_USR",ARM_MSR_CPSR_IMM_USR);
val _ = save_thm("ARM_MSR_CPSR_SYS",ARM_MSR_CPSR_SYS);
val _ = save_thm("ARM_MSR_CPSR_IMM_SYS",ARM_MSR_CPSR_IMM_SYS);

val _ = save_thm("ARM_MSR_SPSR_USR",ARM_MSR_SPSR_USR);
val _ = save_thm("ARM_MSR_SPSR_SYS",ARM_MSR_SPSR_SYS);
val _ = save_thm("ARM_MSR_SPSR_IMM_SYS",ARM_MSR_SPSR_IMM_SYS);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
