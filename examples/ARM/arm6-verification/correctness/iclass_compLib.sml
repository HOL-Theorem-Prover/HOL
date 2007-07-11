(* ========================================================================= *)
(* FILE          : iclass_compLib.sml                                        *)
(* DESCRIPTION   : Provides simpsets for evaluating the models during        *)
(*                 verification.                                             *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2004 - 2005                                               *)
(* ========================================================================= *)

(* interactive use:
 app load ["onestepTheory", "wordsTheory", "armTheory", "coreTheory",
           "lemmasTheory", "interruptsTheory", "iclass_compTheory"];
*)

open HolKernel boolLib bossLib;
open Q computeLib pairTheory
open armTheory coreTheory lemmasTheory interruptsTheory iclass_compTheory;

(* ------------------------------------------------------------------------- *)

fun add_rws f rws =
  let val cmp_set = f()
      val _ = add_thms rws cmp_set
  in
    cmp_set
end;

fun conv_rec nm cnv tm =
  {name = nm, trace = 3, key = SOME([], tm), conv = K (K cnv)};

(* ------------------------------------------------------------------------- *)

val GEQF_INTRO = (GEN_ALL o EQF_INTRO o SPEC_ALL);

fun barm_rws () = add_rws bool_compset 
  [iseq_distinct,GSYM iseq_distinct,iclass_EQ_iclass,iclass2num_thm,
   FST,SND,LET_THM,UNCURRY_DEF, EXEC_INST_def,EXCEPTION_def,
   SWP_def,DECODE_SWP_def, MSR_def,DECODE_MSR_def,
   MRS_def,DECODE_MRS_def, DATA_PROCESSING_def,DECODE_DATAP_def,
   MLA_MUL_def,DECODE_MLA_MUL_def, LDR_STR_def,DECODE_LDR_STR_def,
   LDM_STM_def,DECODE_LDM_STM_def, BRANCH_def,DECODE_BRANCH_def];

val BARM_CONV = CBV_CONV (barm_rws ());
val BARM_ss = simpLib.SSFRAG
  {convs = [conv_rec "BARM_CONV" BARM_CONV ``EXEC_INST a b c``],
   rewrs = [iseq_distinct,iclass_EQ_iclass,iclass2num_thm,
            PROJ_IF_FLAGS_def,DECODE_PSR_def,
            ABS_ARM6_def,NEXT_ARM_def,
            DECODE_IFMODE_SET_IFMODE,CPSR_WRITE_READ,
            REWRITE_RULE [DECODE_IFMODE_SET_IFMODE] DECODE_MODE_THM
            (* SIMP_interrupt2exception,
            SIMP_interrupt2exception2, SIMP_interrupt2exception3,
            SIMP_IS_Dabort,SIMP_PROJ_Dabort,
            GEQF_INTRO NOT_RESET,NOT_RESET2*)],
   congs = [], filter = NONE, ac = [], dprocs = []};

fun Cases_on_arm6inp tm = FULL_STRUCT_CASES_TAC (SPEC tm arm6inp_nchotomy);
fun Cases_on_arm6 tm = FULL_STRUCT_CASES_TAC (SPEC tm arm6_nchotomy);

fun Cases_arm6 (g as (_,w)) =
  let val (Bvar,_) = with_exn dest_forall w (ERR "Cases_arm6" "not a forall")
  in (GEN_TAC THEN FULL_STRUCT_CASES_TAC (Thm.SPEC Bvar arm6_nchotomy)) g
  end
  handle e => raise wrap_exn "Lemmas" "Cases_arm6" e;

(* ------------------------------------------------------------------------- *)

val classes = [`unexec`,`swp`,`mrs_msr`,`data_proc`,`reg_shift`,`ldr`,`str`,
               `br`,`swi_ex`,`cdp_und`,`mrc`,`mcr`,`ldc`,`stc`];

val basic_rws = [FST,SND,LET_THM,UNCURRY_DEF,io_onestepTheory.ADVANCE_def,
  iseq_distinct,GSYM iseq_distinct];

val constant_fold = map CONJUNCTS (CONJ_LIST 17 iclass_comp_thms);
val constant_fold_ldm_stm = map CONJUNCTS (CONJ_LIST 2 ldm_stm_comp_thms);
val constant_fold_mul = [CONJUNCTS mul_comp_thms];
val constant_fold_alu = CONJUNCTS alu_comp_thms;

val ALU_ss = rewrites constant_fold_alu;

(* ------------------------------------------------------------------------- *)

val patterns = map (map (lhs o concl o SPEC_ALL)) constant_fold;

val [constant_fold,constant_fold_ldm_stm,constant_fold_mul] =
  map (map (fn x => INC_IS :: x))
   [constant_fold,constant_fold_ldm_stm,constant_fold_mul];

val inst_convs = map (fn rws =>
  CBV_CONV (add_rws reduceLib.num_compset (rws @ basic_rws))) constant_fold;

fun core_rws () =
  add_rws reduceLib.num_compset
    (basic_rws @ [PCCHANGE_def,DECODE_PSR_def,ABORTINST_def,IC_def,IS_def,
       NXTIC_def,INTSEQ_def,ENDINST_def,DATAABT1_def,DATAABT_def,
       REWRITE_RULE [PIPEAWRITE_def,PIPEBWRITE_def,PIPECWRITE_def,
         PIPEALL_def,PIPEAVAL_def,IREGVAL_def,DINWRITE_def,
         PIPESTATIREGWRITE_def,PIPESTATAWRITE_def,PIPESTATBWRITE_def,
         PIPEAABT_def,RESETLATCH_def,IREGABT2_def,NCPI_def,
         COPROC1_def,FIQACT_def,IRQACT_def,RESETSTART_def] NEXT_ARM6_def]);

val CORE_CONV = CBV_CONV (core_rws());

fun conv_rec2 nm cnv cnst trm =
  {name = nm, trace = 3, key = SOME([cnst]@[``tn``,``tm``], trm),
   conv = K (K cnv)};

fun inst_simpset ((cnst,pat),cnv) = simpLib.SSFRAG
  {convs = [conv_rec "CORE_CONV" CORE_CONV
              ``NEXT_ARM6 (ARM6 d c) (nr,ab,nfiq,nirq,da,cpa,cpb)``] @
           (map (conv_rec2 "INST_CONV" cnv cnst) pat),
   rewrs = [REG_WRITE_WRITE,TEST_OR_COMP_THM],
   congs = [], filter = NONE, ac = [], dprocs = []};

val inst_simpsets
  = map inst_simpset (zip (zip (map Parse.Term
     (classes @ [`ldm`,`stm`,`mla_mul`])) patterns) inst_convs);

val [UNEXEC_ss,SWP_ss,MRS_MSR_ss,DATA_PROC_ss,REG_SHIFT_ss,LDR_ss,STR_ss,
     BR_ss,SWI_EX_ss,CDP_UND_ss,MRC_ss,MCR_ss,LDC_ss,STC_ss,LDM_ss,STM_ss,
     MLA_MUL_ss] = inst_simpsets;

fun inst_tac ss = ASM_SIMP_TAC (std_ss++boolSimps.LET_ss++ss) [];

val [UNEXEC_TAC,SWP_TAC,MRS_MSR_TAC,DATA_PROC_TAC,REG_SHIFT_TAC,LDR_TAC,
     STR_TAC,BR_TAC,SWI_EX_TAC,CDP_UND_TAC,MRC_TAC,MCR_TAC,LDC_TAC,STC_TAC,
     LDM_TAC,STM_TAC,MLA_MUL_TAC] = map inst_tac inst_simpsets;

val [LDM_ITER_CONV,STM_ITER_CONV] = map (fn rws =>
  CBV_CONV (add_rws core_rws (rws @ basic_rws))) constant_fold_ldm_stm;

val MLA_MUL_CONV =
  CBV_CONV (add_rws core_rws ((hd constant_fold_mul) @ basic_rws));

(* ------------------------------------------------------------------------- *)
