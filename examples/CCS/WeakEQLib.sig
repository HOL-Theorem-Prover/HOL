(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

signature WeakEQLib =
sig
  include Abbrev

  val OE_SYM				: thm -> thm
  val OE_TRANS				: thm -> thm -> thm
  val OE_ALL_CONV			: conv
  val OE_THENC				: conv * conv -> conv
  val OE_ORELSEC			: conv * conv -> conv
  val OE_REPEATC			: conv -> conv
  val OE_LHS_CONV_TAC			: conv -> tactic
  val OE_RHS_CONV_TAC			: conv -> tactic

  val STRONG_IMP_WEAK_EQUIV_RULE	: thm -> thm
end

(* last updated: Jun 24, 2017 *)
