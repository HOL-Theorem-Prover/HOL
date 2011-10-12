structure lcsymtacs :> lcsymtacs =
struct

  open Abbrev HolKernel boolLib simpLib BasicProvers

  val all_tac : tactic = ALL_TAC
  fun kall_tac (_: 'a) : tactic = ALL_TAC
  val strip_tac : tactic = STRIP_TAC
  val conj_tac : tactic = CONJ_TAC
  val conj_asm1_tac : tactic = CONJ_ASM1_TAC
  val conj_asm2_tac : tactic = CONJ_ASM2_TAC
  val disj1_tac : tactic = DISJ1_TAC
  val disj2_tac : tactic = DISJ2_TAC
  val gen_tac : tactic = GEN_TAC
  val exists_tac : term -> tactic = EXISTS_TAC
  val suff_tac : term -> tactic = SUFF_TAC
  val rpt = REPEAT
  val reverse = REVERSE
  val ntac = NTAC

  val rewrite_tac : thm list -> tactic = REWRITE_TAC
  val once_rewrite_tac : thm list -> tactic = ONCE_REWRITE_TAC
  val asm_rewrite_tac : thm list -> tactic = ASM_REWRITE_TAC
  val ho_match_mp_tac : thm_tactic = HO_MATCH_MP_TAC
  val match_mp_tac : thm_tactic = MATCH_MP_TAC
  val mp_tac = MP_TAC

  val pop_assum : thm_tactic -> tactic = POP_ASSUM
  val first_assum : thm_tactic -> tactic = FIRST_ASSUM
  val first_x_assum : thm_tactic -> tactic = FIRST_X_ASSUM
  val disch_then = DISCH_THEN

  val qx_gen_tac : term quotation -> tactic = Q.X_GEN_TAC
  val qexists_tac : term quotation -> tactic = Q.EXISTS_TAC
  val qsuff_tac : term quotation -> tactic = Q_TAC SUFF_TAC
  val qid_spec_tac : term quotation -> tactic = Q.ID_SPEC_TAC
  val qspec_then : term quotation -> thm_tactic -> thm -> tactic = Q.SPEC_THEN
  val qspecl_then : term quotation list -> thm_tactic -> thm -> tactic = Q.SPECL_THEN
  val qpat_assum : term quotation -> thm_tactic -> tactic = Q.PAT_ASSUM
  val qmatch_abbrev_tac : term quotation -> tactic = Q.MATCH_ABBREV_TAC
  val qho_match_abbrev_tac : term quotation -> tactic = Q.HO_MATCH_ABBREV_TAC
  val qmatch_rename_tac : term quotation -> string list -> tactic = Q.MATCH_RENAME_TAC
  val qmatch_assum_abbrev_tac : term quotation -> tactic = Q.MATCH_ASSUM_ABBREV_TAC
  val qmatch_assum_rename_tac : term quotation -> string list -> tactic = Q.MATCH_ASSUM_RENAME_TAC

  val rule_assum_tac : (thm -> thm) -> tactic = RULE_ASSUM_TAC
  val assume_tac : thm_tactic = ASSUME_TAC
  val strip_assume_tac : thm_tactic = STRIP_ASSUME_TAC
  val spose_not_then : thm_tactic -> tactic = SPOSE_NOT_THEN

  val qabbrev_tac : term quotation -> tactic = Q.ABBREV_TAC
  val qunabbrev_tac : term quotation -> tactic = Q.UNABBREV_TAC
  val unabbrev_all_tac : tactic = markerLib.UNABBREV_ALL_TAC

  val res_tac : tactic = RES_TAC
  val imp_res_tac : thm_tactic = IMP_RES_TAC

  val map_every : ('a -> tactic) -> 'a list -> tactic = MAP_EVERY

  val decide_tac : tactic = numLib.DECIDE_TAC
  val metis_tac : thm list -> tactic = metisLib.METIS_TAC
  val prove_tac : thm list -> tactic = PROVE_TAC

  val simp_tac = SIMP_TAC
  val asm_simp_tac = ASM_SIMP_TAC
  val full_simp_tac = FULL_SIMP_TAC
  val rw_tac = RW_TAC
  val srw_tac = SRW_TAC
  fun fsrw_tac ssfl thms = let
    val ss = foldl (fn (ssf, ss) => ss ++ ssf) (srw_ss()) ssfl
  in
    full_simp_tac ss thms
  end

  val op>> = op THEN
  val op>- = op THEN1
  val op>| = op THENL

end
