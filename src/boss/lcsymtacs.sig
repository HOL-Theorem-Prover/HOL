signature lcsymtacs =
sig

  include Abbrev
  val all_tac : tactic
  val kall_tac : 'a -> tactic
  val strip_tac : tactic
  val conj_tac : tactic
  val conj_asm1_tac : tactic
  val conj_asm2_tac : tactic
  val disj1_tac : tactic
  val disj2_tac : tactic
  val gen_tac : tactic
  val rpt : tactic -> tactic
  val ntac : int -> tactic -> tactic
  val reverse : tactic -> tactic
  val exists_tac : term -> tactic
  val suff_tac : term -> tactic

  val rewrite_tac : thm list -> tactic
  val once_rewrite_tac : thm list -> tactic
  val asm_rewrite_tac : thm list -> tactic
  val ho_match_mp_tac : thm_tactic
  val mp_tac : thm_tactic
  val match_mp_tac : thm_tactic

  val rule_assum_tac : (thm -> thm) -> tactic
  val pop_assum : thm_tactic -> tactic
  val first_assum : thm_tactic -> tactic
  val first_x_assum : thm_tactic -> tactic
  val disch_then : thm_tactic -> tactic

  val qx_gen_tac : term quotation -> tactic
  val qexists_tac : term quotation -> tactic
  val qsuff_tac : term quotation -> tactic
  val qid_spec_tac : term quotation -> tactic
  val qspec_then : term quotation -> thm_tactic -> thm -> tactic
  val qspecl_then : term quotation list -> thm_tactic -> thm -> tactic
  val qpat_assum : term quotation -> thm_tactic -> tactic
  val qmatch_abbrev_tac : term quotation -> tactic
  val qho_match_abbrev_tac : term quotation -> tactic
  val qmatch_rename_tac : term quotation -> string list -> tactic
  val qmatch_assum_abbrev_tac : term quotation -> tactic
  val qmatch_assum_rename_tac : term quotation -> string list -> tactic

  val assume_tac : thm_tactic
  val strip_assume_tac : thm_tactic
  val spose_not_then : thm_tactic -> tactic

  val qabbrev_tac : term quotation -> tactic
  val qunabbrev_tac : term quotation -> tactic
  val unabbrev_all_tac : tactic

  val res_tac : tactic
  val imp_res_tac : thm_tactic

  val map_every : ('a -> tactic) -> 'a list -> tactic

  val decide_tac : tactic
  val metis_tac : thm list -> tactic
  val prove_tac : thm list -> tactic

  val simp_tac : simpLib.simpset -> thm list -> tactic
  val asm_simp_tac : simpLib.simpset -> thm list -> tactic
  val full_simp_tac : simpLib.simpset -> thm list -> tactic
  val rw_tac : simpLib.simpset -> thm list -> tactic
  val srw_tac : simpLib.ssfrag list -> thm list -> tactic
  val fsrw_tac : simpLib.ssfrag list -> thm list -> tactic

  val >> : tactic * tactic -> tactic
  val >| : tactic * tactic list -> tactic
  val >- : tactic * tactic -> tactic

end
