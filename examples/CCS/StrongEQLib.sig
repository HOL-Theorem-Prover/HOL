(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

signature StrongEQLib =
sig
  include Abbrev

  val S_SYM                     : thm -> thm
  val S_TRANS                   : thm -> thm -> thm
  val S_ALL_CONV                : conv
  val S_THENC                   : conv * conv -> conv
  val S_ORELSEC                 : conv * conv -> conv
  val S_REPEATC                 : conv -> conv
  val S_LHS_CONV_TAC            : conv -> tactic
  val S_RHS_CONV_TAC            : conv -> tactic
  val S_SUB_CONV                : conv -> conv
  val S_TOP_DEPTH_CONV          : conv -> conv
  val S_DEPTH_CONV              : conv -> conv
  val S_SUBST                   : thm -> term -> thm
  val S_LHS_SUBST1_TAC          : thm -> tactic
  val S_LHS_SUBST_TAC           : thm list -> tactic
  val S_RHS_SUBST1_TAC          : thm -> tactic
  val S_RHS_SUBST_TAC           : thm list -> tactic
  val S_SUBST1_TAC              : thm -> tactic
  val S_SUBST_TAC               : thm list -> tactic

end

(* last updated: May 14, 2017 *)
