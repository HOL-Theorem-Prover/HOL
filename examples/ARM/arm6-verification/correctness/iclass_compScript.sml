(* ========================================================================= *)
(* FILE          : iclass_compScript.sml                                     *)
(* DESCRIPTION   : Provides theorems for evaluating the models during        *)
(*                 verification.                                             *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2005                                                      *)
(* ========================================================================= *)

(* interactive use:
 app load ["armTheory", "coreTheory", "lemmasTheory"];
*)

open HolKernel boolLib bossLib;
open Q pairTheory;
open armTheory coreTheory lemmasTheory;

val _ = new_theory "iclass_comp";

(* ------------------------------------------------------------------------- *)

val std_ss = std_ss ++ boolSimps.LET_ss;

val classes = [`unexec`,`swp`,`mrs_msr`,`data_proc`,`reg_shift`,`ldr`,`str`,
               `br`,`swi_ex`,`cdp_und`,`mrc`,`mcr`,`ldc`,`stc`];

val basic_rws =
  [FST,SND,LET_THM,UNCURRY_DEF,io_onestepTheory.ADVANCE_def,
   iseq_distinct,GSYM iseq_distinct];

val basic_rws2 = basic_rws @ [iclass_EQ_iclass,iclass2num_thm];

val the_rws =
  [RP_def,PCWA_def,RWA_def,PIPEBLL_def,BUSA_def,BUSB_def,BORROW_def,COUNT1_def,
   MUL1_def,MSHIFT,NOPC_def,NMREQ_def,NEWINST_def,NXTIS_def,DIN_def,AREG_def,
   NBW_def,NRW_def,NBS_def,MASK_def,SCTRLREGWRITE_def,PSRFBWRITE_def,
   ALUAWRITE_def,ALUBWRITE_def,PSRWA_def];

val the_rws2 =
  [ALU6_def,FIELD_def,SHIFTER_def,RAA_def,RBA_def,PSRA_def,PSRDAT_def];

val SPEC_SIMP =
  (GEN_ALL o
   RIGHT_CONV_RULE (SIMP_CONV (std_ss++rewrites basic_rws2) []) o
   SPEC_ALL);

fun SIMP_SPEC tm = (SPEC_SIMP o SPEC tm);
fun SIMP_SPECL tm = (SPEC_SIMP o SPECL tm);
fun map_rws rws ic = map (SIMP_SPEC ic) rws;

val constant_fold_ldm_stm =
  let val l = map (map_rws ((tl the_rws) @ (tl the_rws2))) [`ldm`,`stm`] in
    [[SIMP_SPEC `ldm` BASELATCH_def,SIMP_SPECL [`ldm`,`tn`] ALU6_def,
      SIMP_SPECL [`ldm`,`tm`] ALU6_def] @ (hd l),hd (tl l)]
  end;

val constant_fold_mul =
  [(SIMP_SPECL [`mla_mul`,`tn`] ALU6_def) :: map_rws (the_rws @ (tl the_rws2))
   `mla_mul`];

val constant_fold =
  (map (map_rws the_rws) classes) @
   constant_fold_ldm_stm @
   constant_fold_mul;

(* Used for ALU evaluation *)
val constant_fold_alu =
 [SIMP_SPEC `br` OFFSET_def,SIMP_SPEC `swi_ex` OFFSET_def] @
  List.concat (map (map_rws the_rws2)
   [`swp`,`mrs_msr`,`data_proc`,`reg_shift`,`ldr`,`str`,
    `br`,`swi_ex`,`mrc`,`ldc`,`stc`]);

val thms = save_thm("iclass_comp_thms",
  LIST_CONJ (map LIST_CONJ constant_fold));

val ldm_stm_thms = save_thm("ldm_stm_comp_thms",
  LIST_CONJ (map LIST_CONJ constant_fold_ldm_stm));

val mul_thms = save_thm("mul_comp_thms",LIST_CONJ (hd constant_fold_mul));
val alu_thms = save_thm("alu_comp_thms",LIST_CONJ constant_fold_alu);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
