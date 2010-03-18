signature lcsymtacs =
sig

  include Abbrev
  val strip_tac : tactic
  val conj_tac : tactic
  val gen_tac : tactic
  val rpt : tactic -> tactic
  val exists_tac : term -> tactic
  val suff_tac : term -> tactic

  val rewrite_tac : thm list -> tactic
  val asm_rewrite_tac : thm list -> tactic
  val ho_match_mp_tac : thm_tactic
  val mp_tac : thm_tactic
  val match_mp_tac : thm_tactic

  val first_assum : thm_tactic -> tactic
  val first_x_assum : thm_tactic -> tactic
  val disch_then : thm_tactic -> tactic

  val qx_gen_tac : term quotation -> tactic
  val qexists_tac : term quotation -> tactic
  val qsuff_tac : term quotation -> tactic

  val res_tac : tactic
  val imp_res_tac : thm_tactic

  val map_every : ('a -> tactic) -> 'a list -> tactic

  val metis_tac : thm list -> tactic
  val prove_tac : thm list -> tactic

  val simp_tac : simpLib.simpset -> thm list -> tactic
  val asm_simp_tac : simpLib.simpset -> thm list -> tactic
  val full_simp_tac : simpLib.simpset -> thm list -> tactic
  val srw_tac : simpLib.ssfrag list -> thm list -> tactic

  val >> : tactic * tactic -> tactic
  val >| : tactic * tactic list -> tactic
  val >- : tactic * tactic -> tactic

end
