(* ========================================================================= *)
(* FILE          : arm_rulesScript.sml                                       *)
(* DESCRIPTION   : Derived rules for the ARM Instruction Set Model           *)
(*                                                                           *)
(* AUTHORS       : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2006 - 2007                                               *)
(* ========================================================================= *)

(* interactive use:
  app load ["systemTheory", "wordsLib", "armLib",
            "arm_evalTheory", "arm_rulesLib", "thumbTheory"];
*)

open HolKernel boolLib Parse bossLib;
open Q arithmeticTheory bitTheory wordsTheory wordsLib;
open updateTheory armTheory systemTheory arm_evalTheory;

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

val _ = wordsLib.guess_lengths();

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

val word_index = METIS_PROVE [word_index_n2w]
  ``!i n. i < dimindex (:'a) ==> ((n2w n):'a word %% i = BIT i n)``;

val CARRY_NZCV = METIS_PROVE [CARRY_def,NZCV_def] ``CARRY (NZCV x) = x %% 29``;

fun DISCH_AND_IMP t =
  (GEN_ALL o SIMP_RULE std_ss [AND_IMP_INTRO] o
   SIMP_RULE std_ss [] o  DISCH t o SPEC_ALL);

val SPEC_TO_PC = (SIMP_RULE (std_ss++arm_rulesLib.ARM_REG_ss) [] o
   INST [`Rd` |-> `15w:word4`] o SPEC_ALL);

val thumb_enc_ = SIMP_CONV (std_ss++wordsLib.SIZES_ss)
  [word_extract_w2w, w2w_id, EXTRACT_ALL_BITS]
  ``(15 >< 0) (w2w (enc_ i) :word32)``;

val _ = augment_srw_ss [boolSimps.LET_ss, SIZES_ss];

val INP_ARM2 = prove(
  `!cp_out mem_out pipe_out RESET FIQ IRQ.
   ((INP_ARM2 (cp_out, mem_out, pipe_out, RESET, FIQ, IRQ)).ireg =
       pipe_out.ireg) /\
   ((INP_ARM2 (cp_out, mem_out, pipe_out, RESET, FIQ, IRQ)).data =
       mem_out.data ++ cp_out.data) /\
   ((INP_ARM2 (cp_out, mem_out, pipe_out, RESET, FIQ, IRQ)).interrupts.Reset =
     RESET) /\
   ((INP_ARM2 (cp_out, mem_out, pipe_out, RESET, FIQ, IRQ)).interrupts.Dabort =
       if mem_out.abort then SOME (LENGTH mem_out.data) else NONE) /\
   ((INP_ARM2 (cp_out, mem_out, pipe_out, RESET, FIQ, IRQ)).absent =
       cp_out.absent)`,
  SRW_TAC [] [INP_ARM2_def]);

val MEM_NO_TRANSFERS = prove(
  `(!write m. NEXT_MEM write read (m, []) = m) /\
    !write m. OUT_MEM write read (m, []) = <|data := []; abort := F|>`,
  SRW_TAC [] [NEXT_MEM_def, OUT_MEM_def, WRITE_MEM_def, READ_MEM_def]);

(* ......................................................................... *)

val EXCEPTION_CONTEXT_def = Define`
  EXCEPTION_CONTEXT read state (mem:'b) cpsr e =
    Abbrev (cpsr = CPSR_READ state.regs.psr) /\
    ~(OUT_NO_PIPE read ((), state, mem:'b)).abort /\
    (state.exception = e)`;

val NOP_CONTEXT_def = Define`
  NOP_CONTEXT read state (mem:'b) cpsr i =
    Abbrev (cpsr = CPSR_READ state.regs.psr) /\
    ~(cpsr:word32 %% 5) /\
    (state.exception = software) /\
    ~CONDITION_PASSED (NZCV cpsr) (enc i) /\
    ~(OUT_NO_PIPE read ((), state, mem:'b)).abort /\
    ((OUT_NO_PIPE read ((), state, mem:'b)).ireg = enc i)`;

val ARM_CONTEXT_def = Define`
  ARM_CONTEXT read state (mem:'b) (Reg,mode,cpsr) i =
    Abbrev (cpsr = CPSR_READ state.regs.psr) /\
    Abbrev (mode = DECODE_MODE ((4 >< 0) cpsr)) /\
    Abbrev (Reg = REG_READ F state.regs.reg mode) /\
    ~(cpsr:word32 %% 5) /\
    (state.exception = software) /\
    CONDITION_PASSED (NZCV cpsr) (enc i) /\
    ~(OUT_NO_PIPE read ((), state, mem:'b)).abort /\
    ((OUT_NO_PIPE read ((), state, mem:'b)).ireg = enc i)`;

val PABORT_CONTEXT_def = Define`
  PABORT_CONTEXT read state (mem:'b) cpsr =
    Abbrev (cpsr = CPSR_READ state.regs.psr) /\
    ~(cpsr:word32 %% 5) /\
    (state.exception = software) /\
    (OUT_NO_PIPE read ((), state, mem:'b)).abort`;

val PABORT_UNDEF = prove(
  `!read state mem Reg mode cpsr.
     PABORT_CONTEXT read state mem cpsr ==>
      ((OUT_NO_PIPE read ((), state, mem:'b)).ireg = enc (UND AL))`,
  SRW_TAC [] [PABORT_CONTEXT_def, OUT_NO_PIPE_def]
    \\ Cases_on `read mem (FETCH_PC state.regs.reg)`
    \\ FULL_SIMP_TAC (srw_ss()) []);

val THUMB_CONTEXT_def = Define`
  THUMB_CONTEXT read state (mem:'b) (Reg,mode,cpsr) i =
    Abbrev (cpsr = CPSR_READ state.regs.psr) /\
    Abbrev (mode = DECODE_MODE ((4 >< 0) cpsr)) /\
    Abbrev (Reg = REG_READ T state.regs.reg mode) /\
    cpsr %% 5 /\
    (state.exception = software) /\
    ~(OUT_NO_PIPE read ((), state, mem:'b)).abort /\
    ((OUT_NO_PIPE read ((), state, mem:'b)).ireg = (w2w (enc_ i)))`;

val CONTXT_ss = rewrites
 [EXCEPTION_CONTEXT_def,NOP_CONTEXT_def,ARM_CONTEXT_def,
  GEN_ALL (MATCH_MP (METIS_PROVE [] ``(l = r) /\ (l ==> q) ==> (l = r /\ q)``)
    (CONJ (SPEC_ALL PABORT_CONTEXT_def) (SPEC_ALL PABORT_UNDEF))),
  THUMB_CONTEXT_def,
  cond_pass_enc_data_proc, cond_pass_enc_data_proc2,
  cond_pass_enc_data_proc3, cond_pass_enc_coproc,
  cond_pass_enc_mla_mul, cond_pass_enc_br, cond_pass_enc_swi,
  cond_pass_enc_ldr_str, cond_pass_enc_ldrh_strh, cond_pass_enc_ldm_stm,
  cond_pass_enc_swp, cond_pass_enc_mrs, cond_pass_enc_msr];

val ARM_ss = rewrites
 [NEXT_1STAGE_def, NEXT_SYSTEM_def, NEXT_ARM_def, NEXT_CP_def, NEXT_NO_PIPE_def,
  INP_ARM1_def, INP_ARM2_def, INP_CP1_def, INP_CP2_def, INP_MEM_def,
  OUT_ARM_def, OUT_CP_def,
  RUN_ARM_def, MEM_NO_TRANSFERS, DECODE_PSR_def, NoTransfers_def,
  thumb_enc_, thumbTheory.thumb_to_arm_enc, interrupt2exception_def,
  CARRY_NZCV, n2w_11, word_bits_n2w, w2n_w2w, word_index, BITS_THM, BIT_ZERO,
  FST_COND_RAND, SND_COND_RAND, (GEN_ALL o SPECL [`b`, `NUMERAL n`]) BIT_def,
  EVAL ``CONDITION_PASSED2 (NZCV x) AL``, CPSR_WRITE_READ,
  DECODE_IFTM_SET_IFTM, DECODE_IFTM_SET_NZCV, DECODE_IFTM_SET_THUMB,
  cond_pass_enc_data_proc, cond_pass_enc_data_proc2,
  cond_pass_enc_data_proc3, cond_pass_enc_coproc,
  cond_pass_enc_mla_mul, cond_pass_enc_br, cond_pass_enc_swi,
  cond_pass_enc_ldr_str, cond_pass_enc_ldrh_strh, cond_pass_enc_ldm_stm,
  cond_pass_enc_swp, cond_pass_enc_mrs, cond_pass_enc_msr];

fun SYMBOLIC_EVAL_CONV frags context =
let val t = parse_in_context (free_vars context)
              `NEXT_1STAGE cp write read
                 ((state, cp_state, mem, ()), (NONE, FIQ, IRQ))`
    val sset = foldl (fn (a,b) => b ++ a)
                 (srw_ss()++armLib.PBETA_ss++ARM_ss) frags
    val c = SIMP_RULE (std_ss++CONTXT_ss) [] (Thm.ASSUME context)
in
  GEN_ALL (Thm.DISCH context (SIMP_CONV sset [c] t))
end;

(* ......................................................................... *)

fun exc_cntxt e =
let val t = (lhs o concl o SPEC_ALL) EXCEPTION_CONTEXT_def in
  subst [``e:exceptions`` |-> e] t
end;

fun nop_cntxt i =
let val t = (lhs o concl o SPEC_ALL) NOP_CONTEXT_def in
  subst [``i:arm_instruction`` |-> i] t
end;

fun cntxt c i =
let
  val t = (lhs o concl o SPEC_ALL) ARM_CONTEXT_def
  val j = subst [``i:arm_instruction`` |-> i] t
  val fvars = free_vars j
in
  list_mk_conj (j :: (map (parse_in_context fvars) c))
end;

fun thumb_cntxt c i =
let
  val t = (lhs o concl o SPEC_ALL) THUMB_CONTEXT_def
  val j = subst [``i:thumb_instruction`` |-> i] t
  val fvars = free_vars j
in
  list_mk_conj (j :: (map (parse_in_context fvars) c))
end;

(* ......................................................................... *)

val EXCEPTION_ss = rewrites
  [EXCEPTION_def,decode_enc_swi,exception2mode_def,exceptions2num_thm];

val EXCEPTION_CONV = SYMBOLIC_EVAL_CONV [EXCEPTION_ss] o exc_cntxt;

val ARM_EXC_RESET  = EXCEPTION_CONV ``reset``;
val ARM_EXC_UNDEF  = EXCEPTION_CONV ``undefined``;
val ARM_EXC_PABORT = EXCEPTION_CONV ``pabort``;
val ARM_EXC_DABORT = EXCEPTION_CONV ``dabort``;
val ARM_EXC_FAST   = EXCEPTION_CONV ``fast``;
val ARM_EXC_INTERRUPT = EXCEPTION_CONV ``interrupt``;

val ARM_RESET = SIMP_CONV (srw_ss()++armLib.PBETA_ss++ARM_ss) []
  ``NEXT_1STAGE cp write read
      ((state, cp_state, mem, ()), (SOME r, FIQ, IRQ))``;

(* ......................................................................... *)

val NOP_ss = rewrites [];

fun eval_nop t = SYMBOLIC_EVAL_CONV [NOP_ss] (nop_cntxt
  (subst [``f:condition -> bool -> word4 ->
              word4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``(f:condition -> bool -> word4 ->
          word4 -> addr_mode1 -> arm_instruction) c s Rd Rm Op2``));

val ARM_AND_NOP = eval_nop ``instruction$AND``;
val ARM_EOR_NOP = eval_nop ``instruction$EOR``;
val ARM_SUB_NOP = eval_nop ``instruction$SUB``;
val ARM_RSB_NOP = eval_nop ``instruction$RSB``;
val ARM_ADD_NOP = eval_nop ``instruction$ADD``;
val ARM_ADC_NOP = eval_nop ``instruction$ADC``;
val ARM_SBC_NOP = eval_nop ``instruction$SBC``;
val ARM_RSC_NOP = eval_nop ``instruction$RSC``;
val ARM_ORR_NOP = eval_nop ``instruction$ORR``;
val ARM_BIC_NOP = eval_nop ``instruction$BIC``;

val eval_nop = SYMBOLIC_EVAL_CONV [NOP_ss] o nop_cntxt;

val ARM_MOV_NOP = eval_nop ``instruction$MOV c s Rd Op2``;
val ARM_MVN_NOP = eval_nop ``instruction$MVN c s Rd Op2``;
val ARM_TST_NOP = eval_nop ``instruction$TST c Rm Op2``;
val ARM_TEQ_NOP = eval_nop ``instruction$TEQ c Rm Op2``;
val ARM_CMP_NOP = eval_nop ``instruction$CMP c Rm Op2``;
val ARM_CMN_NOP = eval_nop ``instruction$CMN c Rm Op2``;

val ARM_MUL_NOP = eval_nop ``instruction$MUL c s Rd Rs Rm``;
val ARM_MLA_NOP = eval_nop ``instruction$MLA c s Rd Rs Rm Rn``;

val ARM_UMULL_NOP = eval_nop ``instruction$UMULL c s RdHi RdLo Rs Rm``;
val ARM_UMLAL_NOP = eval_nop ``instruction$UMLAL c s RdHi RdLo Rs Rm``;
val ARM_SMULL_NOP = eval_nop ``instruction$SMULL c s RdHi RdLo Rs Rm``;
val ARM_SMLAL_NOP = eval_nop ``instruction$SMLAL c s RdHi RdLo Rs Rm``;

val ARM_B_NOP = eval_nop ``instruction$B c offset``;
val ARM_BL_NOP = eval_nop ``instruction$BL c offset``;
val ARM_BX_NOP = eval_nop ``instruction$BX c Rn``;

val ARM_SWI_NOP = eval_nop ``instruction$SWI c imm``;

val ARM_UND_NOP = eval_nop ``instruction$UND c``;

val ARM_LDR_NOP = eval_nop ``instruction$LDR c b opt Rd Rn Op2``;
val ARM_STR_NOP = eval_nop ``instruction$STR c b opt Rd Rn Op2``;
val ARM_LDRH_NOP = eval_nop ``instruction$LDRH c s h opt Rd Rn Op2``;
val ARM_STRH_NOP = eval_nop ``instruction$STRH c opt Rd Rn Op2``;

val ARM_SWP_NOP = eval_nop ``instruction$SWP c b Rd Rm Rn``;

val ARM_LDM_NOP = eval_nop ``instruction$LDM c s opt Rd list``;
val ARM_STM_NOP = eval_nop ``instruction$STM c s opt Rd list``;

val ARM_MRS_NOP = eval_nop ``instruction$MRS c r Rd``;
val ARM_MSR_NOP = eval_nop ``instruction$MSR c psrd op2``;

val ARM_CDP_NOP = eval_nop
  ``instruction$CDP c CPn Cop1 CRd CRn CRm Cop2``;

val ARM_LDC_NOP = eval_nop
  ``instruction$LDC c n options CPn CRd Rn offset``;

val ARM_STC_NOP = eval_nop
  ``instruction$STC c n options CPn CRd Rn offset``;

val ARM_MRC_NOP = eval_nop ``instruction$MRC c CPn Cop1 Rd CRn CRm Cop2``;
val ARM_MCR_NOP = eval_nop ``instruction$MCR c CPn Cop1 Rd CRn CRm Cop2``;

(* ......................................................................... *)

val BRANCH_ss = rewrites
  [BRANCH_def,BRANCH_EXCHANGE_def,decode_enc_br,decode_br_enc];

val ARM_B =
  SYMBOLIC_EVAL_CONV [BRANCH_ss] (cntxt [] ``instruction$B c offset``);

val ARM_BL =
  SYMBOLIC_EVAL_CONV [BRANCH_ss] (cntxt [] ``instruction$BL c offset``);

val ARM_BX =
  (SYMBOLIC_EVAL_CONV [BRANCH_ss] (cntxt [] ``instruction$BX c Rn``));

val SWI_EX_ss =
  rewrites [EXCEPTION_def,exception2mode_def,exceptions2num_thm,
    decode_cp_enc_coproc,decode_enc_swi,decode_enc_coproc,
    decode_27_enc_coproc,thumbTheory.decode_27_enc_coproc_];

val ARM_SWI =
  SYMBOLIC_EVAL_CONV [SWI_EX_ss] (cntxt [] ``instruction$SWI c imm``);

val ARM_UND =
  SYMBOLIC_EVAL_CONV [SWI_EX_ss] (cntxt [] ``instruction$UND c``);

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

val SND_LSL = prove(
  `!n a c. SND (LSL a n c) = a << w2n n`,
  SRW_TAC [] [LSL_def,SHIFT_ZERO,word_0_n2w]);

val LSL_ZERO = (REWRITE_RULE [SHIFT_ZERO,word_0_n2w] o SPEC `0w`) SND_LSL;

val DP_ss =
  rewrites [DATA_PROCESSING_def,ARITHMETIC_def,TEST_OR_COMP_def,ALU_def,
   ALU_ADD,ALU_SUB,LSL_def,LSR_def,ASR_def,ROR_def,AND_def,ORR_def,EOR_def,
   ALU_logic_def,SET_NZC_def,WORD_ADD_0,WORD_SUB_RZERO,WORD_EQ_SUB_RADD,
   WORD_HIGHER_EQ,WORD_NEG_cor,WORD_1COMP_ZERO,REG_READ_INC_PC,
   (SIMP_RULE bool_ss [] o ISPEC `\x:iclass. x = y`) COND_RAND,
   (SIMP_RULE bool_ss [] o ISPEC `\r. REG_READ F r m n`) COND_RAND,
   (SIMP_RULE bool_ss [] o ISPEC `\y. y %% n`) COND_RAND,
   ISPEC `CPSR_READ` COND_RAND,
   PROVE [] ``(if a then (if b then d else c) else c) =
              (if a /\ b then d else c)``,
   decode_enc_data_proc, decode_data_proc_enc,
   decode_enc_data_proc2,decode_data_proc_enc2,
   decode_enc_data_proc3,decode_data_proc_enc3];

val abbrev_mode1 =
  `Abbrev (op2 = ADDR_MODE1 state.regs.reg F mode (cpsr %% 29)
      (IS_DP_IMMEDIATE Op2) ((11 >< 0) (addr_mode1_encode Op2)))`;

val eval_op = SYMBOLIC_EVAL_CONV [DP_ss] o cntxt [`~(Rm = 15w)`,abbrev_mode1];

val ARM_TST = eval_op ``instruction$TST c Rm Op2``;
val ARM_TEQ = eval_op ``instruction$TEQ c Rm Op2``;
val ARM_CMP = eval_op ``instruction$CMP c Rm Op2``;
val ARM_CMN = eval_op ``instruction$CMN c Rm Op2``;

(* ......................................................................... *)

fun eval_op t =
  SYMBOLIC_EVAL_CONV [DP_ss] (cntxt [`~(Rm = 15w)`,abbrev_mode1]
  (subst [``f:condition -> bool -> word4 ->
              word4 -> addr_mode1 -> arm_instruction`` |-> t]
   ``(f:condition -> bool -> word4 ->
          word4 -> addr_mode1 -> arm_instruction) c s Rd Rm Op2``));

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

val ARM_MOV = SYMBOLIC_EVAL_CONV [DP_ss] (cntxt [abbrev_mode1]
  ``instruction$MOV c s Rd Op2``);

val ARM_MVN = SYMBOLIC_EVAL_CONV [DP_ss] (cntxt [abbrev_mode1]
  ``instruction$MVN c s Rd Op2``);

(* ......................................................................... *)

val MLA_MUL_ss = rewrites [MLA_MUL_def,ALU_multiply_def,SET_NZ_def,SET_NZC_def,
    REG_READ_INC_PC,ALU_MUL,ALU_MLA,WORD_ADD_0,REG_READ_WRITE,
   (SIMP_RULE bool_ss [] o ISPEC `\y. y %% n`) COND_RAND,
   ISPEC `CPSR_READ` COND_RAND,
    decode_enc_mla_mul,decode_mla_mul_enc];

val eval_op =
  SYMBOLIC_EVAL_CONV [MLA_MUL_ss] o cntxt [`~(Rd = 15w)`,`~(Rd = Rm)`];

val ARM_MUL = eval_op ``instruction$MUL c s Rd Rm Rs``;
val ARM_MLA = eval_op ``instruction$MLA c s Rd Rm Rs Rn``;

val eval_op = SYMBOLIC_EVAL_CONV [MLA_MUL_ss] o cntxt
  [`~(RdHi = 15w)`,`~(RdLo = 15w)`,`~(RdHi = RdLo)`,
   `~(RdHi = Rm)`, `~(RdLo = Rm)`];

val ARM_UMULL = eval_op ``instruction$UMULL c s RdHi RdLo Rm Rs``;
val ARM_UMLAL = eval_op ``instruction$UMLAL c s RdHi RdLo Rm Rs``;
val ARM_SMULL = eval_op ``instruction$SMULL c s RdHi RdLo Rm Rs``;
val ARM_SMLAL = eval_op ``instruction$SMLAL c s RdHi RdLo Rm Rs``;

(* ......................................................................... *)

val BW = prove(
  `!c f d g0 g1 g2.
    (case (if c then Byte (f d) else Word d) of
       Byte b  -> g0 b
    || Half hw -> g1 hw
    || Word w  -> g2 w) =
   (if c then g0 (f d) else g2 d)`, SRW_TAC [] []);

val LDR_STR_ss =
  rewrites [OUT_MEM_def,NEXT_MEM_def,READ_MEM_def,WRITE_MEM_def,
    LDR_STR_def, LDRH_STRH_def, MEM_WRITE_def, BW, listTheory.HD,
    word_bits_n2w, w2w_n2w, BITS_THM, WORD_ADD_0, REG_READ_INC_PC,
    bool_case_EQ_COND, decode_enc_ldr_str, decode_enc_ldrh_strh,
    decode_ldr_str_enc, decode_ldrh_strh_enc];

val abbrev_mode2 =
  `Abbrev (addr_mode2 = ADDR_MODE2 state.regs.reg F mode (cpsr %% 29)
                (IS_DT_SHIFT_IMMEDIATE offset) opt.Pre opt.Up Rn
                ((11 >< 0) (addr_mode2_encode offset))) /\
   Abbrev (addr = FST addr_mode2) /\
   Abbrev (wb_addr = SND addr_mode2)`;

val abbrev_mode3 =
  `Abbrev (addr_mode3 = ADDR_MODE3 state.regs.reg F mode
                (IS_DTH_IMMEDIATE offset) opt.Pre opt.Up Rn
                ((11 >< 8) (addr_mode3_encode offset))
                ((3 >< 0) (addr_mode3_encode offset))) /\
   Abbrev (addr = FST addr_mode3) /\
   Abbrev (wb_addr = SND addr_mode3)`;

val ARM_LDR =
 SYMBOLIC_EVAL_CONV [LDR_STR_ss]
 (cntxt [abbrev_mode2,`read mem addr = SOME data`,`~(Rn = 15w)`]
  ``instruction$LDR c b opt Rd Rn offset``);

val ARM_LDRH =
 SYMBOLIC_EVAL_CONV [LDR_STR_ss]
 (cntxt [abbrev_mode3,`read mem addr = SOME data`,`~(Rn = 15w)`]
  ``instruction$LDRH c s h opt Rd Rn offset``);

val ARM_LDR_ABORT =
 SYMBOLIC_EVAL_CONV [LDR_STR_ss]
 (cntxt [abbrev_mode2,`read mem addr = NONE`,`~(Rn = 15w)`]
  ``instruction$LDR c b opt Rd Rn offset``);

val ARM_LDRH_ABORT =
 SYMBOLIC_EVAL_CONV [LDR_STR_ss]
 (cntxt [abbrev_mode3,`read mem addr = NONE`,`~(Rn = 15w)`]
  ``instruction$LDRH c s h opt Rd Rn offset``);

val write_mem =
  `write (mem:'b) (addr:word32)
    (if b then Byte ((7 >< 0) (Reg (Rd:word4))) else Word (Reg Rd)) =
    SOME (mem':'b)`;

val ARM_STR = SYMBOLIC_EVAL_CONV [LDR_STR_ss]
 (cntxt [abbrev_mode2,write_mem,`~(Rd = 15w)`,`~(Rn = 15w)`]
  ``instruction$STR c b opt Rd Rn offset``);

val write_mem =
  `write (mem:'b) (addr:word32) (Half ((15 >< 0) (Reg Rd))) = SOME (mem':'b)`;

val ARM_STRH = SYMBOLIC_EVAL_CONV [LDR_STR_ss]
 (cntxt [abbrev_mode3,write_mem,`~(Rd = 15w)`, `~(Rn = 15w)`]
  ``instruction$STRH c opt Rd Rn offset``);

val write_mem =
  `write (mem:'b) (addr:word32)
    (if b then Byte ((7 >< 0) (Reg Rd)) else Word (Reg Rd)) = NONE:'b option`;

val ARM_STR_ABORT = SYMBOLIC_EVAL_CONV [LDR_STR_ss]
 (cntxt [abbrev_mode2,write_mem,`~(Rd = 15w)`,`~(Rn = 15w)`]
  ``instruction$STR c b opt Rd Rn offset``);

val write_mem =
  `write (mem:'b) (addr:word32) (Half ((15 >< 0) (Reg Rd))) = NONE:'b option`;

val ARM_STRH_ABORT = SYMBOLIC_EVAL_CONV [LDR_STR_ss]
 (cntxt [abbrev_mode3,write_mem,`~(Rd = 15w)`, `~(Rn = 15w)`]
  ``instruction$STRH c opt Rd Rn offset``);

(* ......................................................................... *)

val SWP_ss =
  rewrites [OUT_MEM_def,NEXT_MEM_def,READ_MEM_def,WRITE_MEM_def,
    SWP_def,MEM_WRITE_def,BW, listTheory.HD,
    word_bits_n2w, w2w_n2w, BITS_THM, WORD_ADD_0,REG_READ_INC_PC,
    decode_enc_swp,decode_swp_enc];

val write_read_mem =
  `(read mem (Reg Rn) = SOME data) /\
   (write mem (Reg Rn)
    (if b then Byte ((7 >< 0) (Reg Rm)) else Word (Reg Rm)) = SOME (mem':'b))`;

val ARM_SWP = SYMBOLIC_EVAL_CONV [SWP_ss]
  (cntxt [write_read_mem,`~(Rm = 15w)`] ``instruction$SWP c b Rd Rm Rn``);

val ARM_SWP_READ_ABORT =
  SYMBOLIC_EVAL_CONV [SWP_ss] (cntxt [`read mem (Reg Rn) = NONE`]
  ``instruction$SWP c b Rd Rm Rn``);

val write_read_mem =
  `(read mem (Reg Rn) = SOME data) /\
   (write mem (Reg Rn)
    (if b then Byte ((7 >< 0) (Reg Rm)) else Word (Reg Rm)) = NONE:'b option)`;

val ARM_SWP_WRITE_ABORT =
  SYMBOLIC_EVAL_CONV [SWP_ss] (cntxt [write_read_mem,`~(Rm = 15w)`]
  ``instruction$SWP c b Rd Rm Rn``);

(* ......................................................................... *)

val NEXT_MEM_MemRead = prove(
  `!write read mem l. NEXT_MEM write read (mem,MAP MemRead l) = mem`,
  REWRITE_TAC [NEXT_MEM_def] \\ Induct_on `l` \\ SRW_TAC [] [WRITE_MEM_def]
    \\ Cases_on `read mem h` \\ SRW_TAC [] []);

val NEXT_MEM_MemWrite_ = prove(
  `!x write read mem l.
    ~(READ_MEM write read mem (STM_LIST l) x).abort ==>
    (NEXT_MEM write read (mem,STM_LIST l) =
     FOLDL (\m (a,d). THE (write m a (Word d))) mem l)`,
  REWRITE_TAC [STM_LIST_def, NEXT_MEM_def]
    \\ Induct_on `l` \\ SRW_TAC [] [WRITE_MEM_def, READ_MEM_def]
    \\ Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `write mem q (Word r)` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ RES_TAC);

val NEXT_MEM_MemWrite = prove(
  `!write read mem l.
  ~(OUT_MEM write read (mem, STM_LIST l)).abort ==>
   (NEXT_MEM write read (mem, STM_LIST l) =
      FOLDL (\m (a,d). THE (write m a (Word d))) mem l)`,
  METIS_TAC [OUT_MEM_def, NEXT_MEM_MemWrite_]);

val OUT_MEM_MemWrite__ = prove(
  `!f l. IS_NONE (FOLDL
           (\m (r,a). case m of SOME m' -> f m' r a || NONE -> NONE) NONE l)`,
  REWRITE_TAC [optionTheory.IS_NONE_EQ_NONE] \\ Induct_on `l` \\ SRW_TAC [] []
    \\ Cases_on `h` \\ SRW_TAC [] []);

val OUT_MEM_MemWrite_ = prove(
  `!x write read mem l.
    ~(READ_MEM write read mem (STM_LIST l) x).abort =
     IS_SOME (FOLDL (\m (a,d).
                 case m of
                    SOME m' -> write m' a (Word d)
                 || NONE -> NONE) (SOME mem) l)`,
  REWRITE_TAC [STM_LIST_def]
    \\ Induct_on `l` \\ REPEAT STRIP_TAC \\ EQ_TAC
    \\ SRW_TAC [] [READ_MEM_def]
    \\ Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `write mem q (Word r)`
    \\ FULL_SIMP_TAC (srw_ss()) []
    << [RES_TAC, ISPEC_THEN `\m a d. write m a (Word d)`
         ASSUME_TAC OUT_MEM_MemWrite__ \\ FULL_SIMP_TAC (srw_ss()) []]);

val OUT_MEM_MemWrite = prove(
  `!write read mem l.
    ~(OUT_MEM write read (mem, STM_LIST l)).abort =
     IS_SOME (FOLDL (\m (a,d).
                 case m of
                    SOME m' -> write m' a (Word d)
                 || NONE -> NONE) (SOME mem) l)`,
  METIS_TAC [OUT_MEM_def, OUT_MEM_MemWrite_]);

val ZIP_STM_DATA = prove(
  `!P U base l reg r mode.
     ZIP (FST (SND (ADDR_MODE4 P U base l)),
          STM_DATA reg t mode (FST (ADDR_MODE4 P U base l))) =
     MAP (\p. (FST p, REG_READ t reg mode (SND p)))
       (ZIP (FST (SND (ADDR_MODE4 P U base l)), FST (ADDR_MODE4 P U base l)))`,
  SRW_TAC [] [STM_DATA_def, ADDR_MODE4_def, ADDRESS_LIST_def,
    rich_listTheory.LENGTH_GENLIST, listTheory.ZIP_MAP]);

val OUT_MEM_MemRead_ = prove(
  `!d write read l mem.
      ~(READ_MEM write read mem (MAP MemRead l) d).abort ==>
      ((READ_MEM write read mem (MAP MemRead l) d).data =
          d ++ MAP (THE o read mem) l)`,
  Induct_on `l` \\ SRW_TAC [] [READ_MEM_def]
    \\ Cases_on `read mem h` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ METIS_TAC [listTheory.APPEND_ASSOC, rich_listTheory.CONS_APPEND]);

val OUT_MEM_MemRead = prove(
  `!write read l (mem:'b).
      ~((OUT_MEM write read (mem,MAP MemRead l)).abort) ==>
       ((OUT_MEM write read (mem,MAP MemRead l)).data =
         MAP (THE o (read mem)) l)`,
  METIS_TAC [OUT_MEM_def,
    (REWRITE_RULE [listTheory.APPEND] o SPEC `[]`) OUT_MEM_MemRead_]);

val OUT_MEM_MemRead2_ = prove(
  `!d write read l (mem:'b).
      ~(READ_MEM write read mem (MAP MemRead l) d).abort =
      (!x. MEM x l ==> IS_SOME (read mem x))`,
  Induct_on `l` \\ REPEAT STRIP_TAC \\ EQ_TAC \\ SRW_TAC [] [READ_MEM_def]
    \\ Cases_on `read mem h` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ METIS_TAC [optionTheory.IS_SOME_DEF]);

val OUT_MEM_MemRead2 = prove(
  `!write read l (mem:'b).
      ~((OUT_MEM write read (mem,MAP MemRead l)).abort) =
        (!x. MEM x l ==> IS_SOME (read mem x))`,
  METIS_TAC [OUT_MEM_def,
    (REWRITE_RULE [listTheory.APPEND] o SPEC `[]`) OUT_MEM_MemRead2_]);

val FIRSTN_MemRead = prove(
  `!f x P U base l.
     Abbrev (x = ADDR_MODE4 P U base l) ==>
       (FIRSTN (LENGTH (FST x)) (MAP f (FST (SND x))) = MAP f (FST (SND x)))`,
  SRW_TAC [] [markerTheory.Abbrev_def, ADDR_MODE4_def, ADDRESS_LIST_def]
    \\ METIS_TAC [listTheory.LENGTH_MAP, rich_listTheory.LENGTH_GENLIST,
         rich_listTheory.FIRSTN_LENGTH_ID]);

val FIRSTN_MemRead = SIMP_RULE std_ss [markerTheory.Abbrev_def] FIRSTN_MemRead;

val LDM_STM_ss =
  rewrites [LDM_STM_def, NEXT_MEM_MemRead, OUT_MEM_MemRead,
    rich_listTheory.FIRSTN_LENGTH_ID, FIRSTN_MemRead,
    (SIMP_RULE bool_ss [] o ISPEC `\y. y %% n`) COND_RAND,
    ISPEC `CPSR_READ` COND_RAND,
    PROVE [] ``(if a then c else (if b then d else c)) =
               (if a \/ ~b then c else d)``,
    decode_enc_ldm_stm, decode_ldm_stm_enc];

val abbrev_mode4 =
  `Abbrev (addr_mode4 = ADDR_MODE4 opt.Pre opt.Up (Reg (Rd:word4)) list) /\
   Abbrev (rp_list = FST (addr_mode4)) /\
   Abbrev (addr_list = FST (SND (addr_mode4))) /\
   Abbrev (wb = SND (SND (addr_mode4)))`;

val ARM_LDM =
  (SIMP_RULE std_ss [OUT_MEM_MemRead2] o DISCH_AND_IMP abbrev_mode4)
  (SYMBOLIC_EVAL_CONV [LDM_STM_ss] (cntxt
    [`~((OUT_MEM write read (mem,MAP MemRead (FST (SND
           (ADDR_MODE4 opt.Pre opt.Up (Reg Rd) list))))).abort)`]
  ``instruction$LDM c s opt Rd list``));

val ARM_STM =
  (SIMP_RULE std_ss [my_listTheory.FOLDL_MAP2, OUT_MEM_MemWrite] o
   SIMP_RULE std_ss [NEXT_MEM_MemWrite] o
   DISCH_AND_IMP `~(OUT_MEM write read (mem, STM_LIST (MAP (\p.  (FST p,
                       REG_READ F reg' (if s then usr else mode)
                         (SND p))) (ZIP (addr_list,rp_list))))).abort` o
   DISCH_AND_IMP `Abbrev (reg' = if (HD rp_list = Rd) \/ ~opt.Wb \/ (Rd = 15w)
                            then
                              INC_PC F state.regs.reg
                            else
                              REG_WRITE (INC_PC F state.regs.reg)
                                (if s then usr else mode) Rd wb)` o
   DISCH_AND_IMP abbrev_mode4 o
   SIMP_RULE std_ss [ZIP_STM_DATA])
  (SYMBOLIC_EVAL_CONV [LDM_STM_ss] (cntxt []
  ``instruction$STM c s opt Rd list``));

(* ......................................................................... *)

val MRS_MSR_ss = rewrites [MSR_def,MRS_def,DECODE_PSRD_def,
  immediate_enc,decode_enc_msr,decode_msr_enc,decode_enc_mrs,decode_mrs_enc];

val ARM_MSR =
  SYMBOLIC_EVAL_CONV [MRS_MSR_ss]
   (cntxt [`Abbrev ((R,flags,ctrl) = DECODE_PSRD psrd)`]
     ``instruction$MSR c psrd op2``);

val ARM_MRS =
  SYMBOLIC_EVAL_CONV [MRS_MSR_ss] (cntxt [] ``instruction$MRS c r Rd``);

(* ------------------------------------------------------------------------- *)

val ADDRESS_LIST_0 = SIMP_CONV (srw_ss())
  [ADDRESS_LIST_def,rich_listTheory.GENLIST] ``ADDRESS_LIST x 0``;

val COPROC_ss = rewrites [MRC_def,LDC_STC_def,MCR_OUT_def,
  NEXT_MEM_MemRead, OUT_MEM_MemRead, ADDRESS_LIST_0,
  ISPEC `cp_output_absent` COND_RAND, ISPEC `cp_output_data` COND_RAND,
  ISPEC `cp_output_read` COND_RAND, ISPEC `regs_psr` COND_RAND,
  (SIMP_RULE bool_ss [] o ISPEC `\y. y %% n`) COND_RAND,
  ISPEC `CPSR_READ` COND_RAND,
  decode_enc_coproc,decode_cp_enc_coproc,decode_ldc_stc_enc,
  decode_ldc_stc_20_enc,decode_27_enc_coproc,decode_mrc_mcr_rd_enc];

val ARM_PABORT =
  SYMBOLIC_EVAL_CONV [COPROC_ss] ``PABORT_CONTEXT read state (mem:'b) cpsr``;

val ARM_CDP =
  SYMBOLIC_EVAL_CONV [COPROC_ss] (cntxt []
   ``instruction$CDP c CPn Cop1 CRd CRn CRm Cop2``);

val abbrev_mode5 =
  `Abbrev (addr_mode5 = ADDR_MODE5 state.regs.reg mode options.Pre
                           options.Up Rn offset) /\
   Abbrev (addr_list = FST (addr_mode5)) /\
   Abbrev (wb = SND addr_mode5)`;

val ARM_LDC =
  (SIMP_RULE std_ss [OUT_MEM_MemRead2] o DISCH_AND_IMP abbrev_mode5)
  (SYMBOLIC_EVAL_CONV [COPROC_ss]
  (cntxt [`~cp.absent (USER mode) (enc (LDC c n options CPn CRd Rn offset))`,
          `~(OUT_MEM write read (mem,
                MAP MemRead
                  (ADDRESS_LIST
                     (FST
                        (ADDR_MODE5 state.regs.reg mode options.Pre
                           options.Up Rn offset))
                     (cp.n_ldc cp_state (USER mode)
                        (enc (LDC c n options CPn CRd Rn offset)))))).abort`]
   ``instruction$LDC c n options CPn CRd Rn offset``));

val ARM_LDC_ABSENT =
  SYMBOLIC_EVAL_CONV [COPROC_ss]
  (cntxt [`cp.absent (USER mode) (enc (LDC c n options CPn CRd Rn offset))`]
   ``instruction$LDC c n options CPn CRd Rn offset``);

val ARM_STC =
 (SIMP_RULE std_ss [OUT_MEM_MemWrite] o
  SIMP_RULE std_ss [NEXT_MEM_MemWrite] o
  DISCH_AND_IMP `~(OUT_MEM write read (mem, STM_LIST
                   (ZIP (ADDRESS_LIST addr_list (LENGTH data),data)))).abort` o
  DISCH_AND_IMP abbrev_mode5)
  (SYMBOLIC_EVAL_CONV [COPROC_ss]
  (cntxt [`~cp.absent (USER mode) (enc (STC c n options CPn CRd Rn offset))`,
          `Abbrev (data = cp.f_stc cp_state (USER mode)
                      (enc (STC c n options CPn CRd Rn offset)))`]
   ``instruction$STC c n options CPn CRd Rn offset``));

val ARM_STC_ABSENT =
  (SIMP_RULE (srw_ss())
    [STM_LIST_def,OUT_MEM_def,WRITE_MEM_def,NEXT_MEM_def,READ_MEM_def])
  (SYMBOLIC_EVAL_CONV [COPROC_ss]
  (cntxt [`cp.absent (USER mode) (enc (STC c n options CPn CRd Rn offset))`]
   ``instruction$STC c n options CPn CRd Rn offset``));

val ARM_MRC =
  SYMBOLIC_EVAL_CONV [COPROC_ss]
  (cntxt [`~cp.absent (USER mode) (enc (MRC c CPn Cop1 Rd CRn CRm Cop2))`]
   ``instruction$MRC c CPn Cop1 Rd CRn CRm Cop2``);

val ARM_MRC_ABSENT =
  SYMBOLIC_EVAL_CONV [COPROC_ss]
  (cntxt [`cp.absent (USER mode) (enc (MRC c CPn Cop1 Rd CRn CRm Cop2))`]
   ``instruction$MRC c CPn Cop1 Rd CRn CRm Cop2``);

val ARM_MCR =
  SYMBOLIC_EVAL_CONV [COPROC_ss] (cntxt []
   ``instruction$MCR c CPn Cop1 Rd CRn CRm Cop2``);

(* ------------------------------------------------------------------------- *)

val WORD3_NOT_PC = prove(
  `!w:word3. ~(w2w w = 15w:word4)`,
  STRIP_TAC \\ ISPEC_THEN `w` ASSUME_TAC w2n_lt
    \\ FULL_SIMP_TAC (srw_ss()++ARITH_ss) [w2w_def, n2w_11]);

val SHIFT_BY_ZERO_COND = prove(
  `(!w s. (if s = 0w then w else w << w2n s) = w << w2n s) /\
   (!w s. (if s = 0w then w else w >> w2n s) = w >> w2n s) /\
   (!w s. (if s = 0w then w else w #>> w2n s) = w #>> w2n s) /\
    !w s. (if s = 0w then w else w >>> w2n s) = w >>> w2n s`,
  SRW_TAC [] [SHIFT_ZERO, word_0_n2w]);

val w2w_eq_0 = store_thm("w2w_eq_0",
  `!w:'a word. dimindex(:'a) < dimindex(:'b) ==>
       ((w2w w = 0w:'b word) = (w = 0w))`,
  REPEAT STRIP_TAC \\ EQ_TAC \\ SRW_TAC [] [w2w_0]
    \\ Cases_on_word `w`
    \\ FULL_SIMP_TAC (srw_ss())
         [(GSYM o CONJUNCT2) EXP, DECIDE ``0 < n ==> (SUC (n - 1) = n)``,
          DIMINDEX_GT_0, INT_MIN_def, w2w_def, n2w_11, dimword_def]
    \\ `n < 2 ** dimindex (:'b)` by METIS_TAC [TWOEXP_MONO, LESS_TRANS]
    \\ FULL_SIMP_TAC arith_ss []);

val w2w_w2w_ = prove(
  `!w:'a word. dimindex(:'a) <= dimindex(:'b) ==>
               (w2w (w2w w :'b word) = w2w w :'c word)`,
  SRW_TAC [ARITH_ss] [w2w_w2w, WORD_ALL_BITS]);

val concat4 = prove(
  `!w:word8. ((7 >< 4) w :word4) @@ ((3 >< 0) w : word4) = (7 >< 0) w : word32`,
  SRW_TAC [boolSimps.LET_ss,ARITH_ss,fcpLib.FCP_ss]
          [word_extract_def, word_concat_def, word_join_def, word_bits_def,
           word_or_def, word_lsl_def, w2w, fcpTheory.index_sum]
    \\ Cases_on `i < 8`
    \\ Cases_on `4 <= i`
    \\ SRW_TAC [ARITH_ss,fcpLib.FCP_ss] [w2w, fcpTheory.index_sum]);

val WORD_ROL_LSL = prove(
  `!n w:'a word.
        n < dimindex(:'a) /\
        ((dimindex(:'a) - 1 -- dimindex(:'a) - n) w = 0w) ==>
        (w #<< n = w << n)`,
  SRW_TAC [boolSimps.LET_ss,ARITH_ss,fcpLib.FCP_ss]
         [word_rol_def, word_ror_def, word_bits_def, word_lsl_def, word_0]
    \\ PAT_ASSUM `n < dimindex (:'a)` MP_TAC
    \\ PAT_ASSUM `!i. P` (SPEC_THEN `i` IMP_RES_TAC)
    \\ FULL_SIMP_TAC arith_ss [DIMINDEX_GT_0, NOT_LESS_EQUAL]
    << [`n <= i` by DECIDE_TAC,
        Cases_on `n <= i` \\ FULL_SIMP_TAC arith_ss [] <<
        [ALL_TAC, METIS_TAC [SUB_LEFT_ADD, DECIDE ``n < m ==> ~(m <= n:num)``]]]
    \\ ASM_SIMP_TAC std_ss [DIMINDEX_GT_0, LESS_IMP_LESS_OR_EQ,
         ADD_MODULUS_LEFT, ONCE_REWRITE_RULE [ADD_COMM] LESS_EQ_ADD_SUB]
    \\ ASM_SIMP_TAC arith_ss []);

val lem = prove(
  `(!w:word8. (dimindex(:32) - 1 -- dimindex(:32) - 2) (w2w w :word32) = 0w) /\
    !w:word7. (dimindex(:32) - 1 -- dimindex(:32) - 2) (w2w w :word32) = 0w`,
  SRW_TAC [wordsLib.SIZES_ss] [WORD_BITS_ZERO3, word_bits_w2w, w2w_0]);

val lem2 = SIMP_RULE (std_ss++wordsLib.SIZES_ss) [lem]
           (CONJ (ISPECL [`2`, `w2w (w:word8) :word32`] WORD_ROL_LSL)
                 (ISPECL [`2`, `w2w (w:word7) :word32`] WORD_ROL_LSL));

val ROR_30_LSL_2 = prove(
  `(!w:word7. (w2w w):word32 #>> w2n (2w * 15w:word8) = w2w w << 2) /\
    !w:word8. (w2w w):word32 #>> w2n (2w * 15w:word8) = w2w w << 2`,
  REPEAT STRIP_TAC
    \\ ISPECL_THEN [`w2w w :word32`, `2`]
         (ASSUME_TAC o SYM o SIMP_RULE (std_ss++wordsLib.SIZES_ss) [])
         word_rol_def
    \\ SRW_TAC [] [EVAL ``w2n (2w * 15w:word8)``, lem2]);

val w2w_const_mul_w2w = prove(
  `(!w:word5. w2w (4w:word12 * w2w w) = 4w:word32 * w2w w) /\
   (!w:word5. w2w (2w:word8 * w2w w) = 2w:word32 * w2w w) /\
    !w:word8. w2w (4w:word12 * w2w w) = 4w:word32 * w2w w`,
  REPEAT STRIP_TAC
    \\ ISPEC_THEN `w` (ASSUME_TAC o CONV_RULE EVAL) w2n_lt
    \\ ASM_SIMP_TAC (arith_ss++SIZES_ss) [w2w_def,word_mul_n2w,word_extract_def,
         word_bits_n2w,w2n_n2w_bits,BITS_COMP_THM2,BITS_ZEROL]);

val dimindex_11 = EVAL ``dimindex(:11)``;

val imm_sw2sw = prove(
  `!w:11 word. (10 >< 0) (sw2sw w : word24) = w`,
  SRW_TAC [ARITH_ss,fcpLib.FCP_ss]
    [word_extract_def, word_bits_def, dimindex_11, w2w, sw2sw]);

val INC_PC_T = prove(
  `!r. REG_WRITE r usr 15w (FETCH_PC r + 2w) = INC_PC T r`,
  STRIP_TAC \\ EVAL_TAC);

val READ_CASE = prove(
  `(!read (mem:'b) (a:word32) (d:word32).
     (case read mem a of
         NONE -> <|data := k; abort := l|>
      || SOME d -> <|data := m; abort := n|>).abort =
     (case read mem a of NONE -> l || SOME d -> n)) /\
   (!read (mem:'b) (a:word32) (d:word32).
     (case read mem a of
         NONE -> <|data := k; abort := l|>
      || SOME d -> <|data := m; abort := n|>).data =
     (case read mem a of NONE -> k || SOME d -> m))`,
  SRW_TAC [] [] \\ Cases_on `read mem a` \\ SRW_TAC [] []);

val THUMB_DP_ss = rewrites [shift_immediate_shift_register, ADDR_MODE1_def,
   WORD3_NOT_PC, SHIFT_BY_ZERO_COND, ZERO_SHIFT, IS_DP_IMMEDIATE_def,
   EVAL ``w2w (15w:word4) :word8``, EVAL ``32w:word8 <=+ 32w``,
   WORD_SUB_LZERO, WORD_MULT_CLAUSES, LSR_LIMIT, immediate_enc,
   shift_immediate_enc, shift_register_enc, w2w_0, w2w_eq_0, w2w_w2w_];

fun thumb_rule i = SYMBOLIC_EVAL_CONV [DP_ss,THUMB_DP_ss] (thumb_cntxt [] i);

val LSL_1 = thumb_rule ``instruction$LSL_1 Rd Rm imm``;
val LSR_1 = thumb_rule ``instruction$LSR_1 Rd Rm imm``;
val ASR_1 = thumb_rule ``instruction$ASR_1 Rd Rm imm``;

val ADD_3 = thumb_rule ``instruction$ADD_3 Rd Rm Rn``;
val SUB_3 = thumb_rule ``instruction$SUB_3 Rd Rm Rn``;

val ADD_1 = thumb_rule ``instruction$ADD_1 Rd Rm imm``;
val SUB_1 = thumb_rule ``instruction$SUB_1 Rd Rm imm``;

val MOV_1 = thumb_rule ``instruction$MOV_1 Rd imm``;
val CMP_1 = thumb_rule ``instruction$CMP_1 Rm imm``;
val ADD_2 = thumb_rule ``instruction$ADD_2 Rd imm``;
val SUB_2 = thumb_rule ``instruction$SUB_2 Rd imm``;

val AND_  = thumb_rule ``instruction$AND_ Rm Rn``;
val EOR_  = thumb_rule ``instruction$EOR_ Rm Rn``;
val LSL_2 = thumb_rule ``instruction$LSL_2 Rm Rn``;
val LSR_2 = thumb_rule ``instruction$LSR_2 Rm Rn``;
val ASR_2 = thumb_rule ``instruction$ASR_2 Rm Rn``;
val ADC_  = thumb_rule ``instruction$ADC_ Rm Rn``;
val SBC_  = thumb_rule ``instruction$SBC_ Rm Rn``;
val ROR_  = thumb_rule ``instruction$ROR_ Rm Rn``;
val TST_  = thumb_rule ``instruction$TST_ Rm Rn``;
val NEG_  = thumb_rule ``instruction$NEG_ Rm Rn``;
val CMP_2 = thumb_rule ``instruction$CMP_2 Rm Rn``;
val CMN_  = thumb_rule ``instruction$CMN_ Rm Rn``;
val ORR_  = thumb_rule ``instruction$ORR_ Rm Rn``;
val BIC_  = thumb_rule ``instruction$BIC_ Rm Rn``;
val MVN_  = thumb_rule ``instruction$MVN_ Rm Rn``;

val thumb_rule = REWRITE_RULE [ROR_30_LSL_2] o thumb_rule;

val ADD_5  = thumb_rule ``instruction$ADD_5 Rd imm``;
val ADD_6  = thumb_rule ``instruction$ADD_6 Rd imm``;

val ADD_7  = thumb_rule ``instruction$ADD_7 imm``;
val SUB_4  = thumb_rule ``instruction$SUB_4 imm``;

val MUL_  = SYMBOLIC_EVAL_CONV [MLA_MUL_ss,THUMB_DP_ss] (thumb_cntxt
  [`~(w2w Rm = w2w Rn : word4)`] ``instruction$MUL_ Rm Rn``);

val ADD_4  = thumb_rule ``instruction$ADD_4 Rm Rn``;
val CMP_3  = thumb_rule ``instruction$CMP_3 Rm Rn``;
val MOV_3  = thumb_rule ``instruction$MOV_3 Rd Rn``;

val BX_ =
   SYMBOLIC_EVAL_CONV [BRANCH_ss] (thumb_cntxt [] ``instruction$BX_ Rm``);

val THUMB_LDR_STR_ss = rewrites
  [ADDR_MODE2_def, ADDR_MODE3_def, UP_DOWN_def, WORD3_NOT_PC, w2w_w2w_,
   IS_DTH_IMMEDIATE_def, IS_DT_SHIFT_IMMEDIATE_def, EXTRACT_ALL_BITS, concat4,
   LSL_ZERO, w2w_const_mul_w2w, immediate_enc2, immediate_enc3, register_enc3,
   shift_immediate_enc, shift_immediate_enc2];

fun thumb_rule c i =
  SYMBOLIC_EVAL_CONV [LDR_STR_ss,THUMB_LDR_STR_ss] (thumb_cntxt c i);

val LDR_3  = thumb_rule [`read mem (Reg 15w + 4w * w2w imm) = SOME data`]
  ``instruction$LDR_3 Rd imm``;

val STR_2  = thumb_rule
  [`write mem (Reg (w2w Rn) + Reg (w2w Rm)) (Word (Reg (w2w Rd))) =
      SOME (mem':'b)`] ``instruction$STR_2 Rd Rn Rm``;

val STRH_2 = thumb_rule
  [`write mem (Reg (w2w Rn) + Reg (w2w Rm))
      (Half ((15 >< 0) (Reg (w2w Rd)))) = SOME (mem':'b)`]
  ``instruction$STRH_2 Rd Rn Rm``;

val STRB_2 = thumb_rule
  [`write mem (Reg (w2w Rn) + Reg (w2w Rm))
      (Byte ((7 >< 0) (Reg (w2w Rd)))) = SOME (mem':'b)`]
  ``instruction$STRB_2 Rd Rn Rm``;

val eval_op = thumb_rule [`read mem (Reg (w2w Rn) + Reg (w2w Rm)) = SOME data`];

val LDRSB_ = eval_op ``instruction$LDRSB_ Rd Rn Rm``;
val LDR_2  = eval_op ``instruction$LDR_2 Rd Rn Rm``;
val LDRH_2 = eval_op ``instruction$LDRH_2 Rd Rn Rm``;
val LDRB_2 = eval_op ``instruction$LDRB_2 Rd Rn Rm``;
val LDRSH_ = eval_op ``instruction$LDRSH_ Rd Rn Rm``;

val STR_1  = thumb_rule
  [`write mem (Reg (w2w Rn) + 4w * w2w imm) (Word (Reg (w2w Rd))) =
      SOME (mem':'b)`] ``instruction$STR_1 Rd Rn imm``;

val LDR_1  = thumb_rule [`read mem (Reg (w2w Rn) + 4w * w2w imm) = SOME data`]
  ``instruction$LDR_1 Rd Rn imm``;

val STRB_1 = thumb_rule
  [`write mem (Reg (w2w Rn) + w2w imm)
      (Byte ((7 >< 0) (Reg (w2w Rd)))) = SOME (mem':'b)`]
  ``instruction$STRB_1 Rd Rn imm``;

val LDRB_1 = thumb_rule [`read mem (Reg (w2w Rn) + w2w imm) = SOME data`]
  ``instruction$LDRB_1 Rd Rn imm``;

val STRH_1 = thumb_rule
  [`write mem (Reg (w2w Rn) + 2w * w2w imm)
      (Half ((15 >< 0) (Reg (w2w Rd)))) = SOME (mem':'b)`]
  ``instruction$STRH_1 Rd Rn imm``;

val LDRH_1 = thumb_rule
  [`read mem (Reg (w2w Rn) + 2w * w2w imm) = SOME data`]
  ``instruction$LDRH_1 Rd Rn imm``;

val STR_3  = thumb_rule
  [`write mem (Reg 13w + 4w * w2w imm) (Word (Reg (w2w Rd))) = SOME (mem':'b)`]
  ``instruction$STR_3 Rd imm``;

val LDR_4  = thumb_rule [`read mem (Reg 13w + 4w * w2w imm) = SOME data`]
  ``instruction$LDR_4 Rd imm``;

val THUMB_LDM_STM_ss = rewrites [OUT_MEM_MemRead2, ADDR_MODE4_def,
  WB_ADDRESS_def, FIRST_ADDRESS_def, UP_DOWN_def, WORD3_NOT_PC];

fun thumb_rule a i =
  SYMBOLIC_EVAL_CONV [rewrites [WORD3_NOT_PC], LDM_STM_ss] (thumb_cntxt a i);

val PUSH =
   (DISCH_AND_IMP `Abbrev (l = REGISTER_LIST
      (if R then 16384w !! w2w (list:word8) else w2w list))` o
    UNABBREVL_RULE [`l`] o
    SIMP_RULE (std_ss++THUMB_LDM_STM_ss)
      [my_listTheory.FOLDL_MAP2, OUT_MEM_MemWrite] o
    SIMP_RULE std_ss [NEXT_MEM_MemWrite] o
    DISCH_AND_IMP `~(OUT_MEM write read (mem, STM_LIST
                        (MAP (\p. (FST p,REG_READ T reg' mode (SND p)))
                           (ZIP (FST (SND (ADDR_MODE4 T F (Reg 13w) l)),
                               FST (ADDR_MODE4 T F (Reg 13w) l)))))).abort` o
    DISCH_AND_IMP `Abbrev (reg' =
      (if HD (FST (ADDR_MODE4 T F (Reg 13w) l)) = 13w then
         INC_PC T state.regs.reg
       else
         REG_WRITE (INC_PC T state.regs.reg) mode 13w
           (SND (SND (ADDR_MODE4 T F (Reg 13w) l)))))` o
    SIMP_RULE std_ss [ZIP_STM_DATA]) (thumb_rule
   [`Abbrev (l:word16 = if R then 16384w !! w2w (list:word8) else w2w list)` ]
   ``instruction$PUSH R list``);

val POP  = SIMP_RULE (std_ss++THUMB_LDM_STM_ss) [] (thumb_rule
  [`Abbrev (l:word16 = if R then 32768w !! w2w (list:word8) else w2w list)`,
   `~(OUT_MEM write read (mem,
        MAP MemRead (FST (SND (ADDR_MODE4 F T (Reg 13w) l))))).abort`]
  ``instruction$POP R list``);

val LDMIA_  = SIMP_RULE (std_ss++THUMB_LDM_STM_ss) [] (thumb_rule
  [`~(OUT_MEM write read (mem, MAP MemRead
        (FST (SND (ADDR_MODE4 F T (Reg (w2w Rd)) (w2w list)))))).abort`]
  ``instruction$LDMIA_ Rd list``);

val STMIA_  =
  (DISCH_AND_IMP `Abbrev (l = REGISTER_LIST (w2w list))` o
   SIMP_RULE (std_ss++THUMB_LDM_STM_ss)
      [my_listTheory.FOLDL_MAP2, OUT_MEM_MemWrite] o
    SIMP_RULE std_ss [NEXT_MEM_MemWrite] o
   DISCH_AND_IMP
     `~(OUT_MEM write read (mem, STM_LIST
          (MAP (\p. (FST p,REG_READ T reg' mode (SND p)))
             (ZIP (FST (SND (ADDR_MODE4 F T (Reg (w2w Rd)) (w2w list))),
                   FST (ADDR_MODE4 F T (Reg (w2w Rd)) (w2w list))))))).abort` o
   DISCH_AND_IMP `Abbrev (reg' =
      if HD (FST (ADDR_MODE4 F T (Reg (w2w Rd)) (w2w list))) = w2w Rd then
        INC_PC T state.regs.reg
      else
        REG_WRITE (INC_PC T state.regs.reg) mode (w2w Rd)
          (SND (SND (ADDR_MODE4 F T (Reg (w2w Rd)) (w2w list)))))` o
   SIMP_RULE std_ss [ZIP_STM_DATA])
  (thumb_rule [] ``instruction$STMIA_ Rd list``);

val BRANCH_ss = rewrites
  [BRANCH_def,BRANCH_EXCHANGE_def,decode_enc_br,decode_br_enc,sw2sw_sw2sw,
   WORD_EXTRACT_LSL, SHIFT_ZERO, ZERO_SHIFT, WORD_ADD_0, word_extract_w2w,
   EXTRACT_ALL_BITS, WORD_EXTRACT_ZERO3, INC_PC_T, imm_sw2sw,
   dimindex_11, w2w_w2w_];

val B_1 =
  SYMBOLIC_EVAL_CONV [BRANCH_ss] (thumb_cntxt
   [`CONDITION_PASSED2 (NZCV cpsr) c`,
    `~(c = AL)`,`~(c = NV)`] ``instruction$B_1 c imm``);

val B_1_NOP = SYMBOLIC_EVAL_CONV [BRANCH_ss] (thumb_cntxt
  [`~CONDITION_PASSED2 (NZCV cpsr) c`, `~(c = AL)`,`~(c = NV)`]
   ``instruction$B_1 c imm``);

val UND_ = SYMBOLIC_EVAL_CONV [SWI_EX_ss]
  (thumb_cntxt [] ``instruction$UND_``);

val SWI_ = SYMBOLIC_EVAL_CONV [SWI_EX_ss]
  (thumb_cntxt [] ``instruction$SWI_ n``);

val B_2 = SYMBOLIC_EVAL_CONV [BRANCH_ss]
  (thumb_cntxt [] ``instruction$B_2 imm``);

val BL_a0 = SYMBOLIC_EVAL_CONV [DP_ss,THUMB_DP_ss]
  (thumb_cntxt [] ``instruction$BL_a 0w``);

val BL_a = SYMBOLIC_EVAL_CONV [BRANCH_ss]
  (thumb_cntxt [`~(imm = 0w)`] ``instruction$BL_a imm``);

val BL_b = SYMBOLIC_EVAL_CONV [BRANCH_ss]
  (thumb_cntxt [] ``instruction$BL_b imm``);

(* ------------------------------------------------------------------------- *)

val _ = save_thm("ARM_RESET", ARM_RESET);

val _ = save_thm("ARM_EXC_RESET", ARM_EXC_RESET);
val _ = save_thm("ARM_EXC_UNDEF", ARM_EXC_UNDEF);
val _ = save_thm("ARM_EXC_PABORT", ARM_EXC_PABORT);
val _ = save_thm("ARM_EXC_DABORT", ARM_EXC_DABORT);
val _ = save_thm("ARM_EXC_FAST", ARM_EXC_FAST);
val _ = save_thm("ARM_EXC_INTERRUPT", ARM_EXC_INTERRUPT);

val _ = save_thm("ARM_B_NOP",   ARM_B_NOP);
val _ = save_thm("ARM_BL_NOP",  ARM_BL_NOP);
val _ = save_thm("ARM_BX_NOP",  ARM_BX_NOP);
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
val _ = save_thm("ARM_LDRH_NOP", ARM_LDRH_NOP);
val _ = save_thm("ARM_STRH_NOP", ARM_STRH_NOP);
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
val _ = save_thm("ARM_BX",  ARM_BX);
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
val _ = save_thm("ARM_LDRH", ARM_LDRH);
val _ = save_thm("ARM_STRH", ARM_STRH);
val _ = save_thm("ARM_LDM", ARM_LDM);
val _ = save_thm("ARM_STM", ARM_STM);
val _ = save_thm("ARM_SWP", ARM_SWP);

val _ = save_thm("ARM_LDR_ABORT", ARM_LDR_ABORT);
val _ = save_thm("ARM_STR_ABORT", ARM_STR_ABORT);
val _ = save_thm("ARM_LDRH_ABORT", ARM_LDRH_ABORT);
val _ = save_thm("ARM_STRH_ABORT", ARM_STRH_ABORT);
val _ = save_thm("ARM_SWP_READ_ABORT", ARM_SWP_READ_ABORT);
val _ = save_thm("ARM_SWP_WRITE_ABORT", ARM_SWP_WRITE_ABORT);

val _ = save_thm("ARM_MRS",ARM_MRS);
val _ = save_thm("ARM_MSR",ARM_MSR);

val _ = save_thm("ARM_CDP", ARM_CDP);
val _ = save_thm("ARM_LDC", ARM_LDC);
val _ = save_thm("ARM_STC", ARM_STC);
val _ = save_thm("ARM_MRC", ARM_MRC);
val _ = save_thm("ARM_MCR", ARM_MCR);

val _ = save_thm("ARM_LDC_ABSENT", ARM_LDC_ABSENT);
val _ = save_thm("ARM_STC_ABSENT", ARM_STC_ABSENT);
val _ = save_thm("ARM_MRC_ABSENT", ARM_MRC_ABSENT);

val _ = save_thm("LSL_1", LSL_1);
val _ = save_thm("LSR_1", LSR_1);
val _ = save_thm("ASR_1", ASR_1);
val _ = save_thm("ADD_3", ADD_3);
val _ = save_thm("SUB_3", SUB_3);
val _ = save_thm("ADD_1", ADD_1);
val _ = save_thm("SUB_1", SUB_1);
val _ = save_thm("MOV_1", MOV_1);
val _ = save_thm("CMP_1", CMP_1);
val _ = save_thm("ADD_2", ADD_2);
val _ = save_thm("SUB_2", SUB_2);
val _ = save_thm("AND_", AND_);
val _ = save_thm("EOR_", EOR_);
val _ = save_thm("LSL_2", LSL_2);
val _ = save_thm("LSR_2", LSR_2);
val _ = save_thm("ASR_2", ASR_2);
val _ = save_thm("ADC_", ADC_);
val _ = save_thm("SBC_", SBC_);
val _ = save_thm("ROR_", ROR_);
val _ = save_thm("TST_", TST_);
val _ = save_thm("NEG_", NEG_);
val _ = save_thm("CMP_2", CMP_2);
val _ = save_thm("CMN_", CMN_);
val _ = save_thm("ORR_", ORR_);
val _ = save_thm("MUL_", MUL_);
val _ = save_thm("BIC_", BIC_);
val _ = save_thm("MVN_", MVN_);
val _ = save_thm("ADD_4", ADD_4);
val _ = save_thm("CMP_3", CMP_3);
val _ = save_thm("MOV_3", MOV_3);
val _ = save_thm("BX_", BX_);
val _ = save_thm("LDR_3", LDR_3);
val _ = save_thm("STR_2", STR_2);
val _ = save_thm("STRH_2", STRH_2);
val _ = save_thm("STRB_2", STRB_2);
val _ = save_thm("LDRSB_", LDRSB_);
val _ = save_thm("LDR_2", LDR_2);
val _ = save_thm("LDRH_2", LDRH_2);
val _ = save_thm("LDRB_2", LDRB_2);
val _ = save_thm("LDRSH_", LDRSH_);
val _ = save_thm("STR_1", STR_1);
val _ = save_thm("LDR_1", LDR_1);
val _ = save_thm("STRB_1", STRB_1);
val _ = save_thm("LDRB_1", LDRB_1);
val _ = save_thm("STRH_1", STRH_1);
val _ = save_thm("LDRH_1", LDRH_1);
val _ = save_thm("STR_3", STR_3);
val _ = save_thm("LDR_4", LDR_4);
val _ = save_thm("ADD_5", ADD_5);
val _ = save_thm("ADD_6", ADD_6);
val _ = save_thm("ADD_7", ADD_7);
val _ = save_thm("SUB_4", SUB_4);
val _ = save_thm("PUSH", PUSH);
val _ = save_thm("POP", POP);
val _ = save_thm("LDMIA_", LDMIA_);
val _ = save_thm("STMIA_", STMIA_);
val _ = save_thm("B_1", B_1);
val _ = save_thm("UND_", UND_);
val _ = save_thm("SWI_", SWI_);
val _ = save_thm("B_2", B_2);
val _ = save_thm("BL_a0", BL_a0);
val _ = save_thm("BL_a", BL_a);
val _ = save_thm("BL_b", BL_b);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
