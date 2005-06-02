(* ===================================================================== *)
(* FILE          : compLib.sml                                           *)
(* DESCRIPTION   : Provides simpsets for evaluating the models during    *)
(*                 verification.                                         *)
(*                                                                       *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge              *)
(* DATE          : 2001 - 2004                                           *)
(* ===================================================================== *)

(* interactive use:
 app load ["onestepTheory","word32Theory","armTheory",
             "coreTheory","lemmasTheory","interruptsTheory"];
*)

open HolKernel boolLib bossLib Q computeLib pairTheory onestepTheory
     armTheory coreTheory lemmasTheory interruptsTheory;

(* -------------------------------------------------------- *)

fun add_rws f rws =
  let val cmp_set = f()
      val _ = add_thms rws cmp_set
  in
    cmp_set
end;

fun conv_rec nm cnv tm = {name = nm, trace = 3, key = SOME([], tm), conv = K (K cnv)};

(* -------------------------------------------------------- *)

val BIT_W32_NUM = GSYM word32Theory.WORD_BIT_def;
val BITS_W32_NUM = GSYM word32Theory.WORD_BITS_def;

val GEQF_INTRO = (GEN_ALL o EQF_INTRO o SPEC_ALL);

fun barm_rws () = add_rws bool_compset 
  [iclass_distinct,iseq_distinct,GSYM iclass_distinct,GSYM iseq_distinct,
   FST,SND,LET_THM,UNCURRY_DEF, EXEC_INST_def,EXCEPTION_def,
   SWP_def,DECODE_SWP_def, MSR_def,DECODE_MSR_def,
   MRS_def,DECODE_MRS_def, DATA_PROCESSING_def,DECODE_DATAP_def,
   MLA_MUL_def,DECODE_MLA_MUL_def, LDR_STR_def,DECODE_LDR_STR_def,
   LDM_STM_def,DECODE_LDM_STM_def, BRANCH_def,DECODE_BRANCH_def];

val DECODE_IFMODE_SET_IFMODE = REWRITE_RULE [BIT_W32_NUM,BITS_W32_NUM] DECODE_IFMODE_SET_IFMODE;

val BARM_CONV = CBV_CONV (barm_rws ());
val BARM_ss = simpLib.SIMPSET
  {convs = [conv_rec "BARM_CONV" BARM_CONV ``EXEC_INST a b c``],
   rewrs = [iclass_distinct,iseq_distinct,
            PROJ_IF_FLAGS_def,TRIPLE_ARM_EX_def,DECODE_PSR,
            ABS_ARM6_def,NEXT_ARM_def,
            BIT_W32_NUM,BITS_W32_NUM,
            DECODE_IFMODE_SET_IFMODE,CPSR_WRITE_READ,
            REWRITE_RULE [DECODE_IFMODE_SET_IFMODE] DECODE_MODE_THM,
            (* SIMP_interrupt2exception,
            SIMP_interrupt2exception2, SIMP_interrupt2exception3,*)
            SIMP_IS_Dabort,SIMP_PROJ_Dabort,
            GEQF_INTRO NOT_RESET,NOT_RESET2],
   congs = [], filter = NONE, ac = [], dprocs = []};

val std_ss = std_ss ++ boolSimps.LET_ss;
local open io_onestepTheory in
  val stdi_ss = std_ss ++ (rewrites [iclass_distinct,iseq_distinct]) ++
        (rewrites [state_out_accessors, state_out_updates_eq_literal,
           state_out_accfupds, state_out_fupdfupds, state_out_literal_11,
           state_out_fupdfupds_comp, state_out_fupdcanon,
           state_out_fupdcanon_comp]) ;
 val STATE_INP_ss =
         rewrites [state_inp_accessors, state_inp_updates_eq_literal,
           state_inp_accfupds, state_inp_fupdfupds, state_inp_literal_11,
           state_inp_fupdfupds_comp, state_inp_fupdcanon,
           state_inp_fupdcanon_comp];
end;
(* -------------------------------------------------------- *)

val classes = [`unexec`,`swp`,`mrs_msr`,`data_proc`,`reg_shift`,`ldr`,`str`,`br`,`swi_ex`,`cdp_und`];

val basic_rws = [FST,SND,LET_THM,UNCURRY_DEF,io_onestepTheory.ADVANCE_def,iseq_distinct,GSYM iseq_distinct];
val basic_rws2 = basic_rws @ [iclass_distinct,GSYM iclass_distinct];

val the_rws = [RP_def,PCWA_def,RWA_def,PIPEBLL_def,BUSA_def,BUSB_def,
               BORROW_def,COUNT1_def,MUL1_def,MSHIFT,NOPC_def,NMREQ_def,
               NEWINST_def,NXTIS_def,DIN_def,AREG_def,NBW_def,NRW_def,NBS_def,MASK_def,
               SCTRLREGWRITE_def,PSRFBWRITE_def,ALUAWRITE_def,ALUBWRITE_def,PSRWA_def];
val the_rws2 = [ALU6_def,FIELD_def,SHIFTER_def,RAA_def,RBA_def,PSRA_def,
                (PairRules.PBETA_RULE o SIMP_RULE std_ss [GSYM CONCAT_MSR_THM]) PSRDAT_def];

val SPEC_SIMP = (GEN_ALL o RIGHT_CONV_RULE (SIMP_CONV (bool_ss++rewrites basic_rws2) []) o SPEC_ALL);
fun SIMP_SPEC tm = (SPEC_SIMP o SPEC tm);
fun SIMP_SPECL tm = (SPEC_SIMP o SPECL tm);
fun map_rws rws ic = map (SIMP_SPEC ic) rws;

(* -------------------------------------------------------- *)

val constant_fold_ldm_stm =
  let val l = map (map_rws ((tl the_rws) @ (tl the_rws2))) [`ldm`,`stm`] in
    [[SIMP_SPEC `ldm` BASELATCH_def,SIMP_SPECL [`ldm`,`tn`] ALU6_def,SIMP_SPECL [`ldm`,`tm`] ALU6_def] @ (hd l),hd (tl l)]
  end;
val constant_fold_mul = [(SIMP_SPECL [`mla_mul`,`tn`] ALU6_def) :: map_rws (the_rws @ (tl the_rws2)) `mla_mul`];
val constant_fold = (map (map_rws the_rws) classes) @ constant_fold_ldm_stm @ constant_fold_mul;

(* Used for ALU evaluation *)
val constant_fold2 =
 [GSYM ONE_COMP_THREE_ADD,OFFSET_def,LSL_ZERO,LSL_TWO,SND_ROR,
   ALUOUT_ALU_logic,ALUOUT_ADD,ALUOUT_SUB] @
  List.concat (map (map_rws the_rws2)
   [`swp`,`mrs_msr`,`data_proc`,`reg_shift`,`ldr`,`str`,`br`,`swi_ex`]);

val ALU_ss = rewrites constant_fold2;

(* -------------------------------------------------------- *)

val patterns = map (map (lhs o concl o SPEC_ALL)) constant_fold;
val [constant_fold,constant_fold_ldm_stm,constant_fold_mul] =
  map (map (fn x => INC_IS :: x)) [constant_fold,constant_fold_ldm_stm,constant_fold_mul];
val inst_convs = map (fn rws => CBV_CONV (add_rws bool_compset (rws @ basic_rws))) constant_fold;

fun core_rws () =
  add_rws bool_compset
           (basic_rws @ [PCCHANGE_def,DECODE_PSR,ABORTINST_def,IC_def,IS_def,
             NXTIC_def,INTSEQ_def,ENDINST_def,DATAABT1_def,DATAABT_def,
             REWRITE_RULE [PIPEAWRITE_def,PIPEBWRITE_def,PIPECWRITE_def,
               PIPEALL_def,PIPEAVAL_def,IREGVAL_def,DINWRITE_def,
               PIPESTATIREGWRITE_def,PIPESTATAWRITE_def,PIPESTATBWRITE_def,
               PIPEAABT_def,RESETLATCH_def,IREGABT2_def,NCPI_def,
               COPROC1_def,FIQACT_def,IRQACT_def,RESETSTART_def] NEXT_ARM6_def]);
val CORE_CONV = CBV_CONV (core_rws());

fun conv_rec2 nm cnv cnst trm
  = {name = nm, trace = 3, key = SOME([cnst]@[``tn``,``tm``], trm), conv = K (K cnv)};

fun inst_simpset ((cnst,pat),cnv) = simpLib.SIMPSET
  {convs = [conv_rec "CORE_CONV" CORE_CONV ``NEXT_ARM6 (ARM6 d c) (nr,ab,nfiq,nirq,da)``] @
           (map (conv_rec2 "INST_CONV" cnv cnst) pat),
   rewrs = [REG_WRITE_WRITE,TEST_OR_COMP_THM2],
   congs = [], filter = NONE, ac = [], dprocs = []};

val inst_simpsets
  = map inst_simpset (zip (zip (map Parse.Term (classes @ [`ldm`,`stm`,`mla_mul`])) patterns) inst_convs);
val [UNEXEC_ss,SWP_ss,MRS_MSR_ss,DATA_PROC_ss,REG_SHIFT_ss,
     LDR_ss,STR_ss,BR_ss,SWI_EX_ss,UNDEF_ss,LDM_ss,STM_ss,MLA_MUL_ss] = inst_simpsets;

fun inst_tac ss = ASM_SIMP_TAC (std_ss++ss) [];

val [UNEXEC_TAC,SWP_TAC,MRS_MSR_TAC,DATA_PROC_TAC,REG_SHIFT_TAC,
     LDR_TAC,STR_TAC,BR_TAC,SWI_EX_TAC,UNDEF_TAC,LDM_TAC,STM_TAC,MLA_MUL_TAC] = map inst_tac inst_simpsets;

val [LDM_ITER_CONV,STM_ITER_CONV]
   = map (fn rws => CBV_CONV (add_rws core_rws (rws @ basic_rws))) constant_fold_ldm_stm;

val MLA_MUL_CONV = CBV_CONV (add_rws core_rws ((hd constant_fold_mul) @ basic_rws));

(* -------------------------------------------------------- *)
