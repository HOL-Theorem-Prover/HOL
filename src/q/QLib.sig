signature QLib =
sig
  include Abbrev
  val qx_gen_tac : term quotation -> tactic
  val qx_genl_tac : term quotation list -> tactic
  val qx_choose_then : term quotation -> thm_tactic -> thm_tactic
  val qx_choosel_then : term quotation list -> thm_tactic -> thm_tactic
  val qexists_tac : term quotation -> tactic
  val qexistsl_tac : term quotation list -> tactic
  val qexists : term quotation -> tactic
  val qexistsl : term quotation list -> tactic
  val qrefine : term quotation -> tactic
  val qrefinel : term quotation list -> tactic
  val qsuff_tac : term quotation -> tactic
  val qid_spec_tac : term quotation -> tactic
  val qspec_tac : term quotation * term quotation -> tactic
  val qspec_then : term quotation -> thm_tactic -> thm -> tactic
  val qspecl_then : term quotation list -> thm_tactic -> thm -> tactic
  val qhdtm_assum : term quotation -> thm_tactic -> tactic
  val qhdtm_x_assum : term quotation -> thm_tactic -> tactic
  val qpat_assum : term quotation -> thm_tactic -> tactic
  val qpat_x_assum : term quotation -> thm_tactic -> tactic
  val qpat_abbrev_tac : term quotation -> tactic
  val qmatch_abbrev_tac : term quotation -> tactic
  val qho_match_abbrev_tac : term quotation -> tactic
  val qmatch_rename_tac : term quotation -> tactic
  val qmatch_assum_abbrev_tac : term quotation -> tactic
  val qmatch_assum_rename_tac : term quotation -> tactic
  val qmatch_asmsub_rename_tac : term quotation -> tactic
  val qmatch_goalsub_rename_tac : term quotation -> tactic
  val qmatch_asmsub_abbrev_tac : term quotation -> tactic
  val qmatch_goalsub_abbrev_tac : term quotation -> tactic
  val rename1 : term quotation -> tactic
  val rename : term quotation list -> tactic
  val qabbrev_tac : term quotation -> tactic
  val qunabbrev_tac : term quotation -> tactic
  val qunabbrevl_tac : term quotation list -> tactic
  val unabbrev_all_tac : tactic

end
