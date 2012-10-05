structure lcsymtacs :> lcsymtacs =
struct

  open Abbrev HolKernel boolLib

  val all_tac : tactic = Tactical.ALL_TAC
  fun kall_tac (_: 'a) : tactic = Tactical.ALL_TAC
  val eq_tac : tactic = Tactic.EQ_TAC
  val strip_tac : tactic = Tactic.STRIP_TAC
  val conj_tac : tactic = Tactic.CONJ_TAC
  val conj_asm1_tac : tactic = Tactic.CONJ_ASM1_TAC
  val conj_asm2_tac : tactic = Tactic.CONJ_ASM2_TAC
  val disj1_tac : tactic = Tactic.DISJ1_TAC
  val disj2_tac : tactic = Tactic.DISJ2_TAC
  val gen_tac : tactic = Tactic.GEN_TAC
  val exists_tac : term -> tactic = Tactic.EXISTS_TAC
  val suff_tac : term -> tactic = Tactic.SUFF_TAC
  val rpt = Tactical.REPEAT
  val reverse = Tactical.REVERSE
  val ntac = Tactic.NTAC

  val rewrite_tac : thm list -> tactic = Rewrite.REWRITE_TAC
  val once_rewrite_tac : thm list -> tactic = Rewrite.ONCE_REWRITE_TAC
  val asm_rewrite_tac : thm list -> tactic =  Rewrite.ASM_REWRITE_TAC
  val once_asm_rewrite_tac : thm list -> tactic =  Rewrite.ONCE_ASM_REWRITE_TAC
  val ho_match_mp_tac : thm_tactic = Tactic.HO_MATCH_MP_TAC
  val match_mp_tac : thm_tactic = Tactic.MATCH_MP_TAC
  val mp_tac = Tactic.MP_TAC

  val pop_assum : thm_tactic -> tactic = Tactical.POP_ASSUM
  val first_assum : thm_tactic -> tactic = Tactical.FIRST_ASSUM
  val first_x_assum : thm_tactic -> tactic = Tactical.FIRST_X_ASSUM
  val disch_then = Thm_cont.DISCH_THEN

  val qx_gen_tac : term quotation -> tactic = Q.X_GEN_TAC
  val qexists_tac : term quotation -> tactic = Q.EXISTS_TAC
  val qsuff_tac : term quotation -> tactic = Q_TAC SUFF_TAC
  val qid_spec_tac : term quotation -> tactic = Q.ID_SPEC_TAC
  val qspec_then : term quotation -> thm_tactic -> thm -> tactic = Q.SPEC_THEN
  val qspecl_then : term quotation list -> thm_tactic -> thm -> tactic =
     Q.SPECL_THEN
  val qpat_assum : term quotation -> thm_tactic -> tactic = Q.PAT_ASSUM
  val qpat_abbrev_tac : term quotation -> tactic = Q.PAT_ABBREV_TAC
  val qmatch_abbrev_tac : term quotation -> tactic = Q.MATCH_ABBREV_TAC
  val qho_match_abbrev_tac : term quotation -> tactic = Q.HO_MATCH_ABBREV_TAC
  val qmatch_rename_tac : term quotation -> string list -> tactic =
     Q.MATCH_RENAME_TAC
  val qmatch_assum_abbrev_tac : term quotation -> tactic =
     Q.MATCH_ASSUM_ABBREV_TAC
  val qmatch_assum_rename_tac : term quotation -> string list -> tactic =
     Q.MATCH_ASSUM_RENAME_TAC

  val rule_assum_tac : (thm -> thm) -> tactic = Tactic.RULE_ASSUM_TAC
  val assume_tac : thm_tactic = Tactic.ASSUME_TAC
  val strip_assume_tac : thm_tactic = Tactic.STRIP_ASSUME_TAC
  val spose_not_then : thm_tactic -> tactic = BasicProvers.SPOSE_NOT_THEN

  val qabbrev_tac : term quotation -> tactic = Q.ABBREV_TAC
  val qunabbrev_tac : term quotation -> tactic = Q.UNABBREV_TAC
  val unabbrev_all_tac : tactic = markerLib.UNABBREV_ALL_TAC

  val res_tac : tactic = Tactic.RES_TAC
  val imp_res_tac : thm_tactic = Tactic.IMP_RES_TAC

  val map_every : ('a -> tactic) -> 'a list -> tactic = Tactical.MAP_EVERY

  val decide_tac : tactic = numLib.DECIDE_TAC
  val metis_tac : thm list -> tactic = metisLib.METIS_TAC
  val prove_tac : thm list -> tactic = BasicProvers.PROVE_TAC

  val simp_tac = simpLib.SIMP_TAC
  val asm_simp_tac = simpLib.ASM_SIMP_TAC
  val full_simp_tac = simpLib.FULL_SIMP_TAC
  val rev_full_simp_tac = simpLib.REV_FULL_SIMP_TAC
  val rw_tac = BasicProvers.RW_TAC
  val srw_tac = BasicProvers.SRW_TAC

  fun stateful f ssfl thm : tactic =
     let
        val ss = List.foldl (simpLib.++ o Lib.swap) (BasicProvers.srw_ss()) ssfl
     in
        f ss thm
     end

  val fsrw_tac = stateful full_simp_tac
  val rfsrw_tac = stateful rev_full_simp_tac

  val let_arith_list = [boolSimps.LET_ss, numSimps.ARITH_ss, listSimps.LIST_ss]
  val simp = stateful asm_simp_tac let_arith_list
  val lrw = srw_tac let_arith_list
  val lfs = fsrw_tac let_arith_list
  val lrfs = rfsrw_tac let_arith_list

  val rw = srw_tac []
  val fs = fsrw_tac []
  val rfs = rfsrw_tac []

  val op>> = op Tactical.THEN
  val op>- = op Tactical.THEN1
  val op>| = op Tactical.THENL

end
