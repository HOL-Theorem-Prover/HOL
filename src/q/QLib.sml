structure QLib :> QLib =
struct

  open Abbrev boolLib
  val qx_gen_tac : term quotation -> tactic = Q.X_GEN_TAC
  val qx_genl_tac = MAP_EVERY qx_gen_tac
  val qx_choose_then = Q.X_CHOOSE_THEN
  val qexists_tac : term quotation -> tactic = Q.EXISTS_TAC
  val qexistsl_tac = MAP_EVERY qexists_tac
  val qexists = qexists_tac
  val qexistsl = qexistsl_tac
  val qrefine = Q.REFINE_EXISTS_TAC
  val qrefinel = Q.LIST_REFINE_EXISTS_TAC
  val qsuff_tac : term quotation -> tactic = Q_TAC SUFF_TAC
  val qspec_tac = Q.SPEC_TAC
  val qid_spec_tac : term quotation -> tactic = Q.ID_SPEC_TAC
  val qspec_then : term quotation -> thm_tactic -> thm -> tactic = Q.SPEC_THEN
  val qspecl_then : term quotation list -> thm_tactic -> thm -> tactic =
     Q.SPECL_THEN
  val qhdtm_assum = Q.hdtm_assum
  val qhdtm_x_assum = Q.hdtm_x_assum
  val qpat_assum : term quotation -> thm_tactic -> tactic = Q.PAT_ASSUM
  val qpat_x_assum : term quotation -> thm_tactic -> tactic = Q.PAT_X_ASSUM
  val qpat_abbrev_tac : term quotation -> tactic = Q.PAT_ABBREV_TAC
  val qmatch_abbrev_tac : term quotation -> tactic = Q.MATCH_ABBREV_TAC
  val qho_match_abbrev_tac : term quotation -> tactic = Q.HO_MATCH_ABBREV_TAC
  val qmatch_rename_tac : term quotation -> tactic =
     Q.MATCH_RENAME_TAC
  val qmatch_assum_abbrev_tac : term quotation -> tactic =
     Q.MATCH_ASSUM_ABBREV_TAC
  val qmatch_assum_rename_tac : term quotation -> tactic =
     Q.MATCH_ASSUM_RENAME_TAC
  val qmatch_asmsub_rename_tac = Q.MATCH_ASMSUB_RENAME_TAC
  val qmatch_goalsub_rename_tac = Q.MATCH_GOALSUB_RENAME_TAC
  val qmatch_asmsub_abbrev_tac = Q.MATCH_ASMSUB_ABBREV_TAC
  val qmatch_goalsub_abbrev_tac = Q.MATCH_GOALSUB_ABBREV_TAC
  val rename1 = Q.RENAME1_TAC
  val rename = Q.RENAME_TAC

  val qabbrev_tac : term quotation -> tactic = Q.ABBREV_TAC
  val qunabbrev_tac : term quotation -> tactic = Q.UNABBREV_TAC
  val qunabbrevl_tac = MAP_EVERY qunabbrev_tac
  val unabbrev_all_tac : tactic = markerLib.UNABBREV_ALL_TAC

  fun qx_choosel_then [] ttac = ttac
    | qx_choosel_then (q::qs) ttac = qx_choose_then q (qx_choosel_then qs ttac)

end;
