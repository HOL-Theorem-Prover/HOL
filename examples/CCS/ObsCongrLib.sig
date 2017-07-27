(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2017  University of Bologna   (Author: Chun Tian)
 *)

signature ObsCongrLib =
sig
  include Abbrev

  val OC_SYM				: thm -> thm
  val OC_TRANS				: thm -> thm -> thm
  val OC_ALL_CONV			: term -> thm
  val OC_THENC				: conv * conv -> conv
  val OC_ORELSEC			: conv * conv -> conv
  val OC_REPEATC			: conv -> conv
  val OC_LHS_CONV_TAC			: conv -> tactic
  val OC_RHS_CONV_TAC			: conv -> tactic

  val STRONG_IMP_OBS_CONGR_RULE		: thm -> thm
  val OBS_CONGR_IMP_WEAK_EQUIV_RULE	: thm -> thm
end

(* last updated: Jun 24, 2017 *)
