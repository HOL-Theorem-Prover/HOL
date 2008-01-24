(* ========================================================================= *)
(* FILE          : arm_rulesScript.sml                                       *)
(* DESCRIPTION   : Derived rules for the ARM Instruction Set Model           *)
(*                                                                           *)
(* AUTHORS       : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2006 - 2007                                               *)
(* ========================================================================= *)

(* interactive use:
  app load ["systemTheory", "wordsLib", "armLib", "arm_evalTheory"];
*)

open HolKernel boolLib Parse bossLib;
open Q arithmeticTheory bitTheory wordsTheory wordsLib;
open bsubstTheory armTheory systemTheory arm_evalTheory;

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

fun UNABBREVL_RULE l t =
   GEN_ALL (foldl (fn (x,t) => armLib.UNABBREV_RULE x t) (SPEC_ALL t) l);

(* ------------------------------------------------------------------------- *)

val MOD_0 =
  (GSYM o REWRITE_RULE [ZERO_LT_dimword] o SPEC `dimword (:32)`) ZERO_MOD;

val MOD_2EXP_32 =
  simpLib.SIMP_PROVE (std_ss++wordsLib.SIZES_ss) [MOD_2EXP_def,dimword_def]
  ``MOD_2EXP 32 n = n MOD dimword (:32)``;

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

(* ......................................................................... *)

val NOT_MAX_SUC_LT = prove(
  `!a. ~(a = UINT_MAXw:'a word) ==> w2n a + 1 < dimword(:'a)`,
  REWRITE_TAC [GSYM w2n_11]
    \\ RW_TAC std_ss [w2n_lt, DECIDE ``a < b /\ ~(a = b - 1) ==> a + 1 < b``,
          word_T_def, UINT_MAX_def, ZERO_LT_dimword, w2n_n2w]);

val ALU_SUB_ = prove(
  `!n n'. n < dimword(:32) ==>
         (BIT 32 (n + w2n ($- (n2w n') + $- (1w:word32)) + 1) =
          BIT 32 (n + w2n ($- (n2w n'):word32)) \/ (n2w n' = 0w:word32))`,
  REPEAT STRIP_TAC
    \\ REWRITE_TAC [WORD_NEG,GSYM WORD_ADD_ASSOC,WORD_ADD_0,
         EVAL ``1w + (~1w + 1w):word32``]
    \\ Cases_on `n2w n' = 0w:word32`
    << [
      FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss)
        [GSYM ADD_ASSOC,BIT_def,BITS_THM,UINT_MAX_def,WORD_NOT_0,
         ONCE_REWRITE_RULE [ADD_COMM] DIV_MULT_1, word_T_def,w2n_n2w],
      `~(~n2w n' = UINT_MAXw:word32)` by METIS_TAC [WORD_NOT_0,WORD_NOT_NOT]
        \\ IMP_RES_TAC NOT_MAX_SUC_LT
        \\ FULL_SIMP_TAC (std_ss++wordsLib.SIZES_ss)
             [ADD_ASSOC, REWRITE_RULE [GSYM w2n_11, w2n_n2w] word_add_def,
              EVAL ``w2n (1w:word32)``]]);

val ALU_SUB = prove(
  `!c a b. SUB a b c =
     let r = a - b - (if c then 0w else 1w) in
       ((word_msb r, r = 0w,
         if c then
           a >=+ b
         else
           BIT 32 (w2n a + w2n ~b),
         ~(word_msb a = word_msb b) /\ ~(word_msb a = word_msb r)), r)`,
  REPEAT STRIP_TAC \\ Cases_on_word `a` THEN Cases_on_word `b`
    \\ RW_TAC arith_ss [SUB_def,ADD_def,ALU_arith_def,DIVMOD_2EXP,WORD_ADD_0,
         word_hs_def,nzcv_def]
    \\ RW_TAC std_ss [ADD_ASSOC,GSYM word_add_n2w,w2n_n2w,n2w_w2n,n2w_mod,
         MOD_2EXP_32,MOD_PLUS,ZERO_LT_TWOEXP,WORD_ADD_0,
         WORD_NOT,word_sub_def,WORD_NEG_0,MSB_lem,ALU_SUB_,
         (GEN_ALL o SYM o REWRITE_RULE [GSYM MOD_0] o
          INST [`n` |-> `0`] o SPEC_ALL o INST_TYPE [`:'a` |-> `:32`]) n2w_11]
    \\ METIS_TAC [GSYM dimindex_32,WORD_MSB_1COMP,
         GSYM (REWRITE_RULE [word_sub_def] WORD_NOT),
         WORD_ADD_ASSOC,WORD_ADD_LINV,WORD_ADD_0]);

(* ......................................................................... *)

val w2n_n2w_bits = REWRITE_RULE [MOD_DIMINDEX] w2n_n2w;

val word_bits_n2w_32 = (GSYM o SIMP_RULE (std_ss++SIZES_ss) [] o
  INST_TYPE [`:'a` |-> `:32`] o SPECL [`31`,`0`]) word_bits_n2w;

val ALU_MUL = prove(
  `!a b:word32. (31 >< 0) ((w2w a):word64 * w2w b) = a * b`,
  SIMP_TAC (arith_ss++SIZES_ss) [w2w_def,word_mul_n2w,word_extract_def,
         word_bits_n2w,w2n_n2w_bits,BITS_COMP_THM2]
    \\ SIMP_TAC (arith_ss++fcpLib.FCP_ss++SIZES_ss)
         [word_mul_def,word_bits_n2w_32,word_bits_def]);

val ALU_MLA = prove(
  `!a b c:word32. (31 >< 0) (((w2w a):word64) + w2w b * w2w c) = a + b * c`,
  SIMP_TAC (arith_ss++SIZES_ss) [w2w_def,word_mul_n2w,word_add_n2w,
         word_extract_def,word_bits_n2w,w2n_n2w_bits,BITS_COMP_THM2]
    \\ SIMP_TAC (arith_ss++fcpLib.FCP_ss++SIZES_ss) [GSYM word_add_n2w,n2w_w2n,
          GSYM word_mul_def,word_bits_n2w_32,word_bits_def]);

val concat32 = (SIMP_RULE (std_ss++SIZES_ss)
   [fcpTheory.index_sum,w2w_id,EXTRACT_ALL_BITS] o SPECL [`63`,`31`,`0`] o
   INST_TYPE [`:'a` |-> `:64`, `:'b` |-> `:32`,
              `:'c` |-> `:32`, `:'d` |-> `:64`]) CONCAT_EXTRACT;

val mul32 = prove(
  `!a b:word32. (31 >< 0) (((w2w a):word64) * w2w b) = a * b`,
  SIMP_TAC (arith_ss++SIZES_ss) [BITS_COMP_THM2,w2w_def,word_mul_n2w,
         word_extract_def,word_bits_n2w,w2n_n2w_bits]
    \\ SIMP_TAC (arith_ss++fcpLib.FCP_ss++SIZES_ss)
         [word_bits_def,word_bits_n2w_32,GSYM word_mul_def]);

val smul32_lem = prove(
  `!n. BITS 31 0 (a * b) = BITS 31 0 (BITS 31 0 a * BITS 31 0 b)`,
  SIMP_TAC pure_ss [BITS_ZERO3,MOD_TIMES2,ZERO_LT_TWOEXP] \\ REWRITE_TAC []);

val smul32_lem2 = prove(
  `!n. BITS 31 0 (SIGN_EXTEND 32 64 n) = BITS 31 0 n`,
  RW_TAC (pure_ss++boolSimps.LET_ss) [SIGN_EXTEND_def,numLib.num_CONV ``32``,
   (EQT_ELIM o EVAL) ``2 ** 64 - 2 ** 32 = (2 ** 32 - 1) * 2 ** 32``,
   (GSYM o REWRITE_RULE [SYM (numLib.num_CONV ``32``)] o SPEC `31`) BITS_ZERO3,
   BITS_SUM2]
   \\ SIMP_TAC std_ss [BITS_COMP_THM2]);

val smul32 = prove(
  `!a b:word32. (31 >< 0) (((sw2sw a):word64) * sw2sw b) = a * b`,
  SIMP_TAC (arith_ss++SIZES_ss) [BITS_COMP_THM2,w2w_def,sw2sw_def,
         word_extract_def,word_bits_n2w,w2n_n2w_bits,word_mul_n2w,
         Once smul32_lem,smul32_lem2]
    \\ REWRITE_TAC [GSYM smul32_lem]
    \\ SIMP_TAC (arith_ss++fcpLib.FCP_ss++SIZES_ss)
         [word_bits_def,word_bits_n2w_32,GSYM word_mul_def]);

val WORD_UMULL = store_thm("WORD_UMULL",
  `!a:word32 b:word32.
     ((63 >< 32) ((w2w a * w2w b):word64)):word32 @@ (a * b) =
     (w2w a * w2w b):word64`,
  METIS_TAC [concat32,mul32]);

val WORD_SMULL = store_thm("WORD_SMULL",
  `!a:word32 b:word32.
     ((63 >< 32) ((sw2sw a * sw2sw b):word64)):word32 @@ (a * b) =
     (sw2sw a * sw2sw b):word64`,
  METIS_TAC [concat32,smul32]);

(* ------------------------------------------------------------------------- *)

val basic_context =
  [``CONDITION_PASSED2 (NZCV cpsr) c``,
   ``~state.undefined``,
   ``Abbrev (Reg = REG_READ state.registers mode)``,
   ``Abbrev (mode = DECODE_MODE ((4 >< 0) (cpsr:word32)))``,
   ``Abbrev (cpsr = CPSR_READ state.psrs)``];

fun cntxt c i = list_mk_conj
  (mk_eq(``state.memory ((31 >< 2) (state.registers r15))``,i)::
  (c @ basic_context));

val word_index = METIS_PROVE [word_index_n2w]
  ``!i n. i < dimindex (:'a) ==> (((n2w n):'a word) ' i = BIT i n)``;

val CARRY_NZCV = METIS_PROVE [CARRY_def,NZCV_def] ``CARRY (NZCV x) = x ' 29``;

fun DISCH_AND_IMP t =
  (GEN_ALL o SIMP_RULE (srw_ss()) [REG_WRITE_INC_PC,AND_IMP_INTRO] o
   DISCH t o SPEC_ALL);

val PC_ss = rewrites [TO_WRITE_READ6,REG_WRITE_WRITE];

val SPEC_TO_PC = (SIMP_RULE (std_ss++PC_ss) [] o
   INST [`Rd` |-> `15w:word4`] o SPEC_ALL);

val ARM_ss = rewrites [FST_COND_RAND,SND_COND_RAND,NEXT_ARM_MMU,
  RUN_ARM_def,OUT_ARM_def,DECODE_PSR_def,TRANSFERS_def,TRANSFER_def,
  FETCH_PC_def,ADDR30_def,CARRY_NZCV,n2w_11,word_bits_n2w,w2n_w2w,
  word_index,BITS_THM,BIT_ZERO,(GEN_ALL o SPECL [`b`,`NUMERAL n`]) BIT_def,
  OUT_CP_def, RUN_CP_def,
  cond_pass_enc_data_proc,
  cond_pass_enc_data_proc2, cond_pass_enc_data_proc3,cond_pass_enc_coproc,
  cond_pass_enc_mla_mul,cond_pass_enc_br,cond_pass_enc_swi,
  cond_pass_enc_ldr_str,cond_pass_enc_ldm_stm,cond_pass_enc_swp,
  cond_pass_enc_mrs,cond_pass_enc_msr];

fun SYMBOLIC_EVAL_CONV frag context = GEN_ALL (Thm.DISCH context (SIMP_CONV
    (srw_ss()++boolSimps.LET_ss++SIZES_ss++armLib.PBETA_ss++ARM_ss++frag)
    [Thm.ASSUME context] ``NEXT_ARM_MMU cp state``));

(* ......................................................................... *)

val UNDEF_ss =
  rewrites [EXCEPTION_def,decode_enc_swi,exception2mode_def,exceptions2num_thm];

val ARM_UNDEF = SYMBOLIC_EVAL_CONV UNDEF_ss ``state.undefined``;

(* ......................................................................... *)

val nop_context =
  [``Abbrev (cpsr = CPSR_READ state.psrs)``,
   ``~CONDITION_PASSED2 (NZCV cpsr) c``,
   ``~state.undefined``];

fun nop_cntxt i = list_mk_conj
  (mk_eq(``state.memory ((31 >< 2) (state.registers r15))``,i):: nop_context);

val NOP_ss = rewrites [];

fun eval_nop t = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  (subst [``f:condition -> bool -> word4 ->
              word4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``enc ((f:condition -> bool -> word4 ->
             word4 -> addr_mode1 -> arm_instruction) c s Rd Rm Op2)``));

val ARM_AND_NOP = eval_nop ``instruction$AND``
val ARM_EOR_NOP = eval_nop ``instruction$EOR``
val ARM_SUB_NOP = eval_nop ``instruction$SUB``
val ARM_RSB_NOP = eval_nop ``instruction$RSB``
val ARM_ADD_NOP = eval_nop ``instruction$ADD``
val ARM_ADC_NOP = eval_nop ``instruction$ADC``
val ARM_SBC_NOP = eval_nop ``instruction$SBC``
val ARM_RSC_NOP = eval_nop ``instruction$RSC``
val ARM_ORR_NOP = eval_nop ``instruction$ORR``
val ARM_BIC_NOP = eval_nop ``instruction$BIC``

val ARM_MOV_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$MOV c s Rd Op2)``);

val ARM_MVN_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$MVN c s Rd Op2)``);

val ARM_TST_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$TST c Rm Op2)``);

val ARM_TEQ_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$TEQ c Rm Op2)``);

val ARM_CMP_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$CMP c Rm Op2)``);

val ARM_CMN_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$CMN c Rm Op2)``);

val ARM_MUL_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$MUL c s Rd Rs Rm)``);

val ARM_MLA_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$MLA c s Rd Rs Rm Rn)``);

val ARM_UMULL_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$UMULL c s RdLo RdHi Rs Rm)``);

val ARM_UMLAL_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$UMLAL c s RdLo RdHi Rs Rm)``);

val ARM_SMULL_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$SMULL c s RdLo RdHi Rs Rm)``);

val ARM_SMLAL_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$SMLAL c s RdLo RdHi Rs Rm)``);

val ARM_B_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$B c offset)``);

val ARM_BL_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$BL c offset)``);

val ARM_SWI_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$SWI c)``);

val ARM_UND_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$UND c)``);

val ARM_LDR_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$LDR c b opt Rd Rn Op2)``);

val ARM_STR_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$STR c b opt Rd Rn Op2)``);

val ARM_SWP_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$SWP c b Rd Rm Rn)``);

val ARM_LDM_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$LDM c s opt Rd list)``);

val ARM_STM_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$STM c s opt Rd list)``);

val ARM_MRS_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$MRS c r Rd)``);

val ARM_MSR_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$MSR c psrd op2)``);

val ARM_CDP_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$CDP c CPn Cop1 CRd CRn CRm Cop2)``);

val ARM_LDC_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$LDC c n options CPn CRd Rn offset)``);

val ARM_STC_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$STC c n options CPn CRd Rn offset)``);

val ARM_MRC_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$MRC c CPn Cop1 Rd CRn CRm Cop2)``);

val ARM_MCR_NOP = SYMBOLIC_EVAL_CONV NOP_ss (nop_cntxt
  ``enc (instruction$MCR c CPn Cop1 Rd CRn CRm Cop2)``);

(* ......................................................................... *)

val BRANCH_ss = rewrites [BRANCH_def,REG_READ_def,decode_enc_br,decode_br_enc];

val ARM_B = UNABBREVL_RULE [`cpsr`,`Reg`,`mode`]
  (SYMBOLIC_EVAL_CONV BRANCH_ss (cntxt [] ``enc (instruction$B c offset)``));

val ARM_BL = UNABBREVL_RULE [`Reg`]
  (SYMBOLIC_EVAL_CONV BRANCH_ss (cntxt [] ``enc (instruction$BL c offset)``));

val SWI_EX_ss =
  rewrites [EXCEPTION_def,exception2mode_def,exceptions2num_thm,
    decode_cp_enc_coproc,decode_enc_swi,decode_enc_coproc,decode_27_enc_coproc];

val ARM_SWI = UNABBREVL_RULE [`Reg`,`mode`]
  (SYMBOLIC_EVAL_CONV SWI_EX_ss (cntxt [] ``enc (instruction$SWI c)``));

val ARM_UND = UNABBREVL_RULE [`Reg`,`mode`]
  (SYMBOLIC_EVAL_CONV SWI_EX_ss (cntxt [] ``enc (instruction$UND c)``));

(* ......................................................................... *)

val LSL_NOT_ZERO = prove(
  `!n. ~(n = 0w:word5) ==> ~(w2w n = 0w:word8)`,
  Cases_word \\ RW_TAC bool_ss [dimword_def,ZERO_MOD,ZERO_LT_TWOEXP,
         w2w_def,n2w_11,w2n_n2w,dimindex_5,dimindex_8]
    \\ ASSUME_TAC (DECIDE ``5 < 8``) \\ IMP_RES_TAC TWOEXP_MONO
    \\ METIS_TAC [MOD_2EXP_LT,LESS_TRANS,LESS_MOD]);

val WORD_NEG_cor =
  METIS_PROVE [WORD_NEG,WORD_ADD_ASSOC,WORD_ADD_COMM,word_sub_def]
  ``~a + b + 1w = b - a``;

val WORD_1COMP_ZERO =
  METIS_PROVE [WORD_NOT_NOT,WORD_NOT_T] ``!a. (~a = 0w) = (a = Tw)``;

val SND_ROR = prove(
  `!a n c. SND (ROR a n c) = a #>> w2n n`,
  RW_TAC std_ss [ROR_def,LSL_def,SHIFT_ZERO,word_0_n2w]);

val DP_ss =
  rewrites [DATA_PROCESSING_def,ARITHMETIC_def,TEST_OR_COMP_def,ALU_def,
   ALU_ADD,ALU_SUB,LSL_def,LSR_def,AND_def,ORR_def,EOR_def,ALU_logic_def,
   SET_NZC_def,WORD_ADD_0,WORD_SUB_RZERO,WORD_EQ_SUB_RADD,WORD_HIGHER_EQ,
   REG_READ_INC_PC,WORD_NEG_cor,WORD_1COMP_ZERO,
   (SIMP_RULE bool_ss [] o ISPEC `\x:iclass. x = y`) COND_RAND,
   (SIMP_RULE bool_ss [] o ISPEC `\r. REG_READ r m n`) COND_RAND,
   decode_enc_data_proc, decode_data_proc_enc,
   decode_enc_data_proc2,decode_data_proc_enc2,
   decode_enc_data_proc3,decode_data_proc_enc3];

val abbrev_mode1 =
  ``Abbrev (op2 = ADDR_MODE1 state.registers mode ((cpsr:word32) ' 29)
      (IS_DP_IMMEDIATE Op2) ((11 >< 0) (addr_mode1_encode Op2)))``;

val ARM_TST = SYMBOLIC_EVAL_CONV DP_ss (cntxt
  [``~(Rm = 15w:word4)``,abbrev_mode1] ``enc (instruction$TST c Rm Op2)``);

val ARM_TEQ = SYMBOLIC_EVAL_CONV DP_ss (cntxt
  [``~(Rm = 15w:word4)``,abbrev_mode1] ``enc (instruction$TEQ c Rm Op2)``);

val ARM_CMP = SYMBOLIC_EVAL_CONV DP_ss (cntxt
  [``~(Rm = 15w:word4)``,abbrev_mode1] ``enc (instruction$CMP c Rm Op2)``);

val ARM_CMN = SYMBOLIC_EVAL_CONV DP_ss (cntxt
  [``~(Rm = 15w:word4)``,abbrev_mode1] ``enc (instruction$CMN c Rm Op2)``);

(* ......................................................................... *)

fun eval_op t =
  SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(Rm = 15w:word4)``,abbrev_mode1]
  (subst [``f:condition -> bool -> word4 ->
              word4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``enc ((f:condition -> bool -> word4 ->
             word4 -> addr_mode1 -> arm_instruction) c s Rd Rm Op2)``));

val ARM_AND = eval_op ``instruction$AND``;
val ARM_EOR = eval_op ``instruction$EOR``;
val ARM_SUB = eval_op ``instruction$SUB``;
val ARM_RSB = eval_op ``instruction$RSB``;
val ARM_ADD = eval_op ``instruction$ADD``;
val ARM_ORR = eval_op ``instruction$ORR``;
val ARM_BIC = eval_op ``instruction$BIC``;
val ARM_ADC = eval_op ``instruction$ADC``;
val ARM_SBC = eval_op ``instruction$SBC``;
val ARM_RSC = eval_op ``instruction$RSC``;

val ARM_MOV =
  SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(Rm = 15w:word4)``,abbrev_mode1]
  ``enc (instruction$MOV c s Rd Op2)``);

val ARM_MVN =
  SYMBOLIC_EVAL_CONV DP_ss (cntxt [``~(Rm = 15w:word4)``,abbrev_mode1]
  ``enc (instruction$MVN c s Rd Op2)``);

(* ......................................................................... *)

val MLA_MUL_ss = rewrites [MLA_MUL_def,ALU_multiply_def,SET_NZC_def,
    REG_READ_INC_PC,ALU_MUL,ALU_MLA,WORD_ADD_0,REG_READ_WRITE,
    decode_enc_mla_mul,decode_mla_mul_enc];

val ARM_MUL = SYMBOLIC_EVAL_CONV MLA_MUL_ss (cntxt
  [``~(Rd = 15w:word4)``,``~(Rd = Rm:word4)``]
  ``enc (instruction$MUL c s Rd Rm Rs)``);

val ARM_MLA = SYMBOLIC_EVAL_CONV MLA_MUL_ss (cntxt
  [``~(Rd = 15w:word4)``,``~(Rd = Rm:word4)``]
  ``enc (instruction$MLA c s Rd Rm Rs Rn)``);

val ARM_UMULL = SYMBOLIC_EVAL_CONV MLA_MUL_ss (cntxt
  [``~(RdHi = 15w:word4)``,``~(RdLo = 15w:word4)``,``~(RdHi = RdLo:word4)``,
   ``~(RdHi = Rm:word4)``,``~(RdLo = Rm:word4)``]
  ``enc (instruction$UMULL c s RdLo RdHi Rm Rs)``);

val ARM_UMLAL = SYMBOLIC_EVAL_CONV MLA_MUL_ss (cntxt
  [``~(RdHi = 15w:word4)``,``~(RdLo = 15w:word4)``,``~(RdHi = RdLo:word4)``,
   ``~(RdHi = Rm:word4)``,``~(RdLo = Rm:word4)``]
  ``enc (instruction$UMLAL c s RdLo RdHi Rm Rs)``);

val ARM_SMULL = SYMBOLIC_EVAL_CONV MLA_MUL_ss (cntxt
  [``~(RdHi = 15w:word4)``,``~(RdLo = 15w:word4)``,``~(RdHi = RdLo:word4)``,
   ``~(RdHi = Rm:word4)``,``~(RdLo = Rm:word4)``]
  ``enc (instruction$SMULL c s RdLo RdHi Rm Rs)``);

val ARM_SMLAL = SYMBOLIC_EVAL_CONV MLA_MUL_ss (cntxt
  [``~(RdHi = 15w:word4)``,``~(RdLo = 15w:word4)``,``~(RdHi = RdLo:word4)``,
   ``~(RdHi = Rm:word4)``,``~(RdLo = Rm:word4)``]
  ``enc (instruction$SMLAL c s RdLo RdHi Rm Rs)``);

(* ......................................................................... *)

val BW = prove(
  `!c f d g0 g1 g2.
    (case (if c then Byte (f d) else Word d) of
       Byte b  -> g0 b
    || Half hw -> g1 hw
    || Word w  -> g2 w) =
   (if c then g0 (f d) else g2 d)`, SRW_TAC [] []);

val LDR_STR_ss =
  rewrites [LDR_STR_def,MEM_WRITE_def,BW,
    listTheory.HD,word_bits_n2w,w2w_n2w,BITS_THM,
    WORD_ADD_0,REG_WRITE_INC_PC,REG_READ_WRITE,REG_READ_INC_PC,
    decode_enc_ldr_str,decode_ldr_str_enc];

val abbrev_mode2 =
  ``Abbrev (addr_mode2 = ADDR_MODE2 state.registers mode ((cpsr:word32) ' 29)
                (IS_DT_SHIFT_IMMEDIATE offset) opt.Pre opt.Up Rn
                ((11 >< 0) (addr_mode2_encode offset))) /\
    Abbrev (addr = FST addr_mode2) /\
    Abbrev (wb_addr = SND addr_mode2)``;

val ARM_LDR = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [abbrev_mode2,``~(Rn = 15w:word4)``]
  ``enc (instruction$LDR c b opt Rd Rn offset)``);

val ARM_STR = SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [abbrev_mode2,``~(Rd = 15w:word4)``,``~(Rn = 15w:word4)``]
  ``enc (instruction$STR c b opt Rd Rn offset)``);

val ARM_LDR_PC = SIMP_RULE (std_ss++PC_ss) []
 (SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [abbrev_mode2,``Rn = 15w:word4``]
  ``enc (instruction$LDR c b opt Rd Rn offset)``));

val ARM_STR_PC = SIMP_RULE (std_ss++PC_ss) []
 (SYMBOLIC_EVAL_CONV LDR_STR_ss
 (cntxt [abbrev_mode2,``~(Rd = 15w:word4)``,``Rn = 15w:word4``]
  ``enc (instruction$STR c b opt Rd Rn offset)``));

(* ......................................................................... *)

val SWP_ss =
  rewrites [SWP_def,MEM_WRITE_def,BW,
    listTheory.HD,word_bits_n2w,w2w_n2w,BITS_THM,
    WORD_ADD_0,REG_WRITE_INC_PC,REG_READ_WRITE,REG_READ_INC_PC,
    decode_enc_swp,decode_swp_enc];

val ARM_SWP = SYMBOLIC_EVAL_CONV SWP_ss (cntxt [``~(Rm = 15w:word4)``]
  ``enc (instruction$SWP c b Rd Rm Rn)``);

(* ......................................................................... *)

val FOLDL_INDUCT = prove(
  `!f e P l. (!x y. P x ==> P (f x y)) /\ P e ==> P (FOLDL f e l)`,
  Induct_on `l` \\ ASM_SIMP_TAC (srw_ss()++listSimps.LIST_ss) []);

val TRANSFER_LDM_ = prove(
  `!x y. (SND (SND x) = mem) ==>
         (SND (SND (TRANSFER cpi x (MemRead y))) = mem)`,
  Cases_on `x` \\ Cases_on `r` \\ SRW_TAC [] [TRANSFER_def]
    \\ ASM_REWRITE_TAC []);

val TRANSFER_LDM = SIMP_RULE std_ss [TRANSFER_LDM_]
   (ISPECL [`\x y. TRANSFER cpi x (MemRead y)`,
     `(cpin:word32 option list,data:word32 list,mem:mem)`,
     `\q:word32 option list # word32 list # mem. SND (SND q) = mem`]
    FOLDL_INDUCT);

val TRANSFER_LDM2___ = prove(
  `!data cpin m l.
     LENGTH (FST (SND
       (FOLDL (\x y. TRANSFER F x (MemRead y)) (cpin,data,m) l))) =
     LENGTH data + LENGTH l`,
   Induct_on `l`
     \\ ASM_SIMP_TAC (srw_ss()++listSimps.LIST_ss++ARITH_ss) [TRANSFER_def]);

val TRANSFER_LDM2__ = prove(
  `!rd cpin m l.
     LENGTH (FST (SND
       (FOLDL (\x y. TRANSFER F x (MemRead y)) (cpin,[],m)
          (ADDRESS_LIST rd (LENGTH l))))) = LENGTH l`,
  SIMP_TAC list_ss [TRANSFER_LDM2___,ADDRESS_LIST_def,
   rich_listTheory.LENGTH_GENLIST]);

val TRANSFER_LDM2_ = prove(
  `!m d l. FST (SND (FOLDL (\x y. TRANSFER F x (MemRead y)) (cpin,d,m) l)) =
             d ++ MAP (\x. m (ADDR30 x)) l`,
 Induct_on `l` \\ ASM_SIMP_TAC (srw_ss()++listSimps.LIST_ss) [TRANSFER_def,
    GSYM rich_listTheory.SNOC_APPEND,my_listTheory.APPEND_SNOC1]);

val TRANSFER_LDM2 = prove(
  `!cpin m P U rd l.
     let addr_mode4 = ADDR_MODE4 P U rd l in
       FIRSTN (LENGTH (FST addr_mode4))
         (FST (SND (FOLDL (\x y. TRANSFER F x (MemRead y)) (cpin,[],m)
            (FST (SND addr_mode4))))) =
       MAP (m o ADDR30) (FST (SND addr_mode4))`,
  REPEAT STRIP_TAC
    \\ `!rd. FIRSTN (LENGTH (REGISTER_LIST l))
          (FST (SND (FOLDL (\x y. TRANSFER F x (MemRead y)) (cpin,[],m)
             (ADDRESS_LIST (FIRST_ADDRESS P U rd
               (WB_ADDRESS U rd (LENGTH (REGISTER_LIST l))))
                 (LENGTH (REGISTER_LIST l)))))) =
          (FST (SND (FOLDL (\x y. TRANSFER F x (MemRead y)) (cpin,[],m)
             (ADDRESS_LIST (FIRST_ADDRESS P U rd
               (WB_ADDRESS U rd (LENGTH (REGISTER_LIST l))))
                 (LENGTH (REGISTER_LIST l))))))`
    by METIS_TAC [TRANSFER_LDM2__,rich_listTheory.FIRSTN_LENGTH_ID]
    \\ SRW_TAC [boolSimps.LET_ss] [ADDR_MODE4_def]
    \\ SRW_TAC []
         [ADDRESS_LIST_def,TRANSFER_LDM2_,my_listTheory.MAP_GENLIST]
    \\ MATCH_MP_TAC my_listTheory.GENLIST_FUN_EQ
    \\ SIMP_TAC std_ss []);

val TRANSFER_LDM2 = SIMP_RULE (bool_ss++boolSimps.LET_ss) [] TRANSFER_LDM2;

val TRANSFER_STM = prove(
  `!cpin data m r mode l. 
      SND (SND (FOLDL (TRANSFER F) (cpin,data,m) (STM_LIST r mode l))) =
      FOLDL (\mem (rp,rd). MEM_WRITE mem rd (Word (REG_READ r mode rp))) m l`,
  Induct_on `l` \\ TRY (Cases_on `h`)
    \\ ASM_SIMP_TAC (srw_ss()++listSimps.LIST_ss) [TRANSFER_def,STM_LIST_def]
    \\ ASM_SIMP_TAC std_ss [GSYM STM_LIST_def]);
     
val LDM_STM_ss =
  rewrites [LDM_STM_def,MEM_WRITE_def,
    rich_listTheory.FIRSTN_LENGTH_ID,my_listTheory.FOLDL_MAP2,
    listTheory.HD,word_bits_n2w,w2w_n2w,BITS_THM,
    WORD_ADD_0,REG_WRITE_INC_PC,REG_READ_WRITE,REG_READ_INC_PC,
    TRANSFER_LDM, TRANSFER_LDM2, TRANSFER_STM, LDM_LIST_def,
    decode_enc_ldm_stm,decode_ldm_stm_enc];

val abbrev_mode4 =
  ``Abbrev (addr_mode4 = ADDR_MODE4 opt.Pre opt.Up (Reg (Rd:word4)) list) /\
    Abbrev (rp_list = FST addr_mode4) /\
    Abbrev (addr_list = FST (SND addr_mode4)) /\
    Abbrev (wb = SND (SND addr_mode4))``;

val ARM_LDM = (GEN_ALL o Thm.DISCH abbrev_mode4 o
   SIMP_RULE std_ss [Thm.ASSUME abbrev_mode4] o SPEC_ALL)
  (SYMBOLIC_EVAL_CONV LDM_STM_ss (cntxt [``Abbrev (l = REGISTER_LIST list)``]
  ``enc (instruction$LDM c s opt Rd list)``));

val ARM_STM = (GEN_ALL o Thm.DISCH abbrev_mode4 o
   SIMP_RULE std_ss [Thm.ASSUME abbrev_mode4] o SPEC_ALL)
  (SYMBOLIC_EVAL_CONV LDM_STM_ss (cntxt [``Abbrev (l = REGISTER_LIST list)``]
  ``enc (instruction$STM c s opt Rd list)``));

(* ......................................................................... *)

(*
val lem = METIS_PROVE [DECIDE ``!i. ~(28 <= i \/ i <= 7) = 8 <= i /\ i <= 27``]
 ``!rm. (\i b. 28 <= i /\ (rm:word32) ' i \/
                8 <= i /\ i <= 27 /\ b \/ i <= 7 /\ rm ' i) =
   (\i b. if i <= 7 \/ 28 <= i then rm ' i else b)``;

val lem2 = METIS_PROVE [DECIDE ``!i. ~(28 <= i) = 8 <= i /\ i <= 27 \/ i <= 7``]
 ``!rm. (\i b. 28 <= i /\ (rm:word32) ' i \/
                8 <= i /\ i <= 27 /\ b \/ i <= 7 /\ b) =
   (\i b. if 28 <= i then rm ' i else b)``;

val lem3 = SIMP_RULE (std_ss++armLib.PBETA_ss) [] (prove(
  `!op2 c.  let (I,R,bit19,bit16,Rm,opnd) =
              DECODE_MSR (enc (instruction$MSR c SPSR_a op2)) in
     (R \/ (~bit19 /\ bit16)) \/ (~bit19 /\ ~bit16)`,
  Cases \\ SIMP_TAC std_ss [DECODE_PSRD_def,decode_msr_enc]));
*)

val MRS_MSR_ss = rewrites [MSR_def,MRS_def,DECODE_PSRD_def,
  immediate_enc,decode_enc_msr,decode_msr_enc,decode_enc_mrs,decode_mrs_enc];

val ARM_MSR = UNABBREVL_RULE [`Reg`]
  (SYMBOLIC_EVAL_CONV MRS_MSR_ss (cntxt []
   ``enc (instruction$MSR c psrd op2)``));

val ARM_MRS = UNABBREVL_RULE [`Reg`]
  (SYMBOLIC_EVAL_CONV MRS_MSR_ss (cntxt [] ``enc (instruction$MRS c r Rd)``));

(* ------------------------------------------------------------------------- *)

val EVERY_N_LDC = prove(
  `!n. EVERY (\x. ~IS_SOME x) (GENLIST (K NONE) n)`,
  STRIP_TAC \\ MATCH_MP_TAC my_listTheory.EVERY_GENLIST \\ SRW_TAC [] []);

val SYM_WORD_RULE = ONCE_REWRITE_RULE
  [Thm.INST_TYPE [alpha |-> ``:word4``] EQ_SYM_EQ];

val ADDRESS_LIST_0 = SIMP_CONV (srw_ss())
  [ADDRESS_LIST_def,rich_listTheory.GENLIST] ``ADDRESS_LIST x 0``;

val ZIP_COND = SIMP_CONV (bool_ss++boolSimps.LIFT_COND_ss) []
   ``ZIP (if a then b else c, if a then d else e)``;

val COPROC_ss = rewrites [SYM_WORD_RULE MRC_def,LDC_STC_def,MCR_OUT_def,
  PROVE [] ``!b x y. (if ~b then x else y) = (if b then y else x)``,
  ISPEC `cp_output_absent` COND_RAND, ISPEC `cp_output_data` COND_RAND,
  ISPEC `regs_reg` COND_RAND, ISPEC `regs_psr` COND_RAND,
  ISPEC `SPLITP IS_NONE` COND_RAND, ISPEC `SPLITP IS_NONE` COND_RAND,
  ISPEC `LENGTH` COND_RAND, ISPEC `ADDRESS_LIST x` COND_RAND,
  ISPEC `FOLDL f e` COND_RAND,
  FST_COND_RAND, ZIP_COND, EVAL ``ELL 1 [a; b]``, ADDRESS_LIST_0,
  rich_listTheory.LENGTH_GENLIST, CONJUNCT1 rich_listTheory.SPLITP,
  MATCH_MP (SPEC_ALL my_listTheory.SPLITP_EVERY) (SPEC_ALL EVERY_N_LDC),
  decode_enc_coproc,decode_cp_enc_coproc,decode_ldc_stc_enc,
  decode_ldc_stc_20_enc,decode_27_enc_coproc,decode_mrc_mcr_rd_enc];

val ARM_CDP = UNABBREVL_RULE [`Reg`]
  (SYMBOLIC_EVAL_CONV COPROC_ss (cntxt []
   ``enc (instruction$CDP c CPn Cop1 CRd CRn CRm Cop2)``));

val ARM_LDC = UNABBREVL_RULE [`Reg`]
  (SYMBOLIC_EVAL_CONV COPROC_ss (cntxt []
   ``enc (instruction$LDC c n options CPn CRd Rn offset)``));

val ARM_STC = UNABBREVL_RULE [`Reg`]
  (SYMBOLIC_EVAL_CONV COPROC_ss (cntxt []
   ``enc (instruction$STC c n options CPn CRd Rn offset)``));

val ARM_MRC = (UNABBREVL_RULE [`Reg`] o SYM_WORD_RULE)
  (SYMBOLIC_EVAL_CONV COPROC_ss (cntxt []
   ``enc (instruction$MRC c CPn Cop1 Rd CRn CRm Cop2)``));

val ARM_MCR = UNABBREVL_RULE [`Reg`]
  (SYMBOLIC_EVAL_CONV COPROC_ss (cntxt []
   ``enc (instruction$MCR c CPn Cop1 Rd CRn CRm Cop2)``));

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
val _ = save_thm("ARM_UMULL_NOP", ARM_UMULL_NOP);
val _ = save_thm("ARM_UMLAL_NOP", ARM_UMLAL_NOP);
val _ = save_thm("ARM_SMULL_NOP", ARM_SMULL_NOP);
val _ = save_thm("ARM_SMLAL_NOP", ARM_SMLAL_NOP);
val _ = save_thm("ARM_LDR_NOP", ARM_LDR_NOP);
val _ = save_thm("ARM_STR_NOP", ARM_STR_NOP);
val _ = save_thm("ARM_LDM_NOP", ARM_LDM_NOP);
val _ = save_thm("ARM_STM_NOP", ARM_STM_NOP);
val _ = save_thm("ARM_SWP_NOP", ARM_SWP_NOP);
val _ = save_thm("ARM_MRS_NOP", ARM_MRS_NOP);
val _ = save_thm("ARM_MSR_NOP", ARM_MSR_NOP);
val _ = save_thm("ARM_UND_NOP", ARM_UND_NOP);
val _ = save_thm("ARM_CDP_NOP", ARM_CDP_NOP);
val _ = save_thm("ARM_LDC_NOP", ARM_LDC_NOP);
val _ = save_thm("ARM_STC_NOP", ARM_STC_NOP);
val _ = save_thm("ARM_MRC_NOP", ARM_MRC_NOP);
val _ = save_thm("ARM_MCR_NOP", ARM_MCR_NOP);

val _ = save_thm("ARM_B",   ARM_B);
val _ = save_thm("ARM_BL",  ARM_BL);
val _ = save_thm("ARM_SWI", ARM_SWI);
val _ = save_thm("ARM_UND", ARM_UND);

val _ = save_thm("ARM_TST", ARM_TST);
val _ = save_thm("ARM_TEQ", ARM_TEQ);
val _ = save_thm("ARM_CMP", ARM_CMP);
val _ = save_thm("ARM_CMN", ARM_CMN);

val _ = save_thm("ARM_AND", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_AND);
val _ = save_thm("ARM_EOR", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_EOR);
val _ = save_thm("ARM_SUB", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SUB);
val _ = save_thm("ARM_RSB", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSB);
val _ = save_thm("ARM_ADD", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADD);
val _ = save_thm("ARM_ORR", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ORR);
val _ = save_thm("ARM_MOV", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MOV);
val _ = save_thm("ARM_BIC", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_BIC);
val _ = save_thm("ARM_MVN", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_MVN);
val _ = save_thm("ARM_ADC", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_ADC);
val _ = save_thm("ARM_SBC", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_SBC);
val _ = save_thm("ARM_RSC", DISCH_AND_IMP `~(Rd = 15w:word4)` ARM_RSC);

val _ = save_thm("ARM_AND_PC", SPEC_TO_PC ARM_AND);
val _ = save_thm("ARM_EOR_PC", SPEC_TO_PC ARM_EOR);
val _ = save_thm("ARM_SUB_PC", SPEC_TO_PC ARM_SUB);
val _ = save_thm("ARM_RSB_PC", SPEC_TO_PC ARM_RSB);
val _ = save_thm("ARM_ADD_PC", SPEC_TO_PC ARM_ADD);
val _ = save_thm("ARM_ORR_PC", SPEC_TO_PC ARM_ORR);
val _ = save_thm("ARM_MOV_PC", SPEC_TO_PC ARM_MOV);
val _ = save_thm("ARM_BIC_PC", SPEC_TO_PC ARM_BIC);
val _ = save_thm("ARM_MVN_PC", SPEC_TO_PC ARM_MVN);
val _ = save_thm("ARM_ADC_PC", SPEC_TO_PC ARM_ADC);
val _ = save_thm("ARM_SBC_PC", SPEC_TO_PC ARM_SBC);
val _ = save_thm("ARM_RSC_PC", SPEC_TO_PC ARM_RSC);

val _ = save_thm("ARM_MUL", ARM_MUL);
val _ = save_thm("ARM_MLA", ARM_MLA);
val _ = save_thm("ARM_UMULL", ARM_UMULL);
val _ = save_thm("ARM_UMLAL", ARM_UMLAL);
val _ = save_thm("ARM_SMULL", ARM_SMULL);
val _ = save_thm("ARM_SMLAL", ARM_SMLAL);

val _ = save_thm("ARM_LDR", ARM_LDR);
val _ = save_thm("ARM_STR", ARM_STR);
val _ = save_thm("ARM_LDM", ARM_LDM);
val _ = save_thm("ARM_STM", ARM_STM);
val _ = save_thm("ARM_SWP", ARM_SWP);
val _ = save_thm("ARM_LDR_PC", ARM_LDR_PC);
val _ = save_thm("ARM_STR_PC", ARM_STR_PC);

val _ = save_thm("ARM_MRS",ARM_MRS);
val _ = save_thm("ARM_MSR",ARM_MSR);

val _ = save_thm("ARM_CDP", ARM_CDP);
val _ = save_thm("ARM_LDC", ARM_LDC);
val _ = save_thm("ARM_STC", ARM_STC);
val _ = save_thm("ARM_MRC", ARM_MRC);
val _ = save_thm("ARM_MCR", ARM_MCR);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
