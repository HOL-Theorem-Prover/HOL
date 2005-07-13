(* =====================================================================*)
(* FILE          : res_rules.sig                                        *)
(* DESCRIPTION   : Signature for restricted quantification inference    *)
(*                 rules 					        *)
(* AUTHOR	 : P Curzon 					        *)
(* DATE		 : May 1993						*)
(* UPDATED       : Joe Hurd, October 2001                               *)
(*                                                                      *)
(* =====================================================================*)

signature res_quanTools =
sig
  include Abbrev

  (* Term constructors/destructors *)
  val mk_res_forall          : term * term * term -> term
  val mk_res_exists          : term * term * term -> term
  val mk_res_exists_unique   : term * term * term -> term
  val mk_res_select          : term * term * term -> term
  val mk_res_abstract        : term * term * term -> term
  val dest_res_forall        : term -> term * term * term
  val dest_res_exists        : term -> term * term * term
  val dest_res_exists_unique : term -> term * term * term
  val dest_res_select        : term -> term * term * term
  val dest_res_abstract      : term -> term * term * term
  val is_res_forall          : term -> bool
  val is_res_exists          : term -> bool
  val is_res_exists_unique   : term -> bool
  val is_res_select          : term -> bool
  val is_res_abstract        : term -> bool
  val list_mk_res_forall     : (term * term) list * term -> term
  val list_mk_res_exists     : (term * term) list * term -> term
  val strip_res_forall       : term -> (term * term) list * term
  val strip_res_exists       : term -> (term * term) list * term

  (* Conversions *)
  val RES_FORALL_CONV        : conv
  val RES_EXISTS_CONV        : conv
  val RES_EXISTS_UNIQUE_CONV : conv
  val RES_SELECT_CONV        : conv
  val IMP_RES_FORALL_CONV    : conv
  val RES_FORALL_AND_CONV    : conv
  val AND_RES_FORALL_CONV    : conv
  val RES_FORALL_SWAP_CONV   : conv
  val RESQ_REWRITE1_CONV     : thm list -> thm -> conv

  (* Derived rules *)
  val RESQ_HALF_SPEC         : term -> rule
  val RESQ_HALF_SPECL        : term list -> rule
  val RESQ_SPEC              : term -> rule
  val RESQ_SPECL             : term list -> rule
  val RESQ_MATCH_MP          : thm -> thm -> thm
  val RESQ_REWR_CANON        : thm -> thm

  (* Tactics *)
  val RESQ_HALF_EXISTS_THEN  : thm_tactical
  val RESQ_CHOOSE_THEN       : thm_tactical
  val RESQ_STRIP_THM_THEN    : thm_tactical
  val RESQ_GEN_THEN          : thm_tactic -> tactic
  val RESQ_STRIP_GOAL_THEN   : thm_tactic -> tactic
  val RESQ_STRIP_ASSUME_TAC  : thm_tactic
  val RESQ_GEN_TAC           : tactic
  val RESQ_STRIP_TAC         : tactic
  val RESQ_EXISTS_TAC        : term -> tactic
  val RESQ_IMP_RES_THEN      : thm_tactic -> thm_tactic
  val RESQ_RES_THEN          : thm_tactic -> tactic
  val RESQ_IMP_RES_TAC       : thm_tactic
  val RESQ_RES_TAC           : tactic
  val RESQ_REWRITE1_TAC      : thm_tactic

  (* Restricted quantifier elimination using the simplifier *)
  val resq_SS                : simpLib.ssfrag
  val resq_ss                : simpLib.simpset
  val RESQ_TAC               : tactic

  (* Versions of some restricted quantifier tools using term quotations *)
  val Q_RESQ_EXISTS_TAC      : term quotation -> tactic
  val Q_RESQ_HALF_SPEC       : term quotation -> rule
  val Q_RESQ_HALF_SPECL      : term quotation list -> rule
  val Q_RESQ_SPEC            : term quotation -> rule
  val Q_RESQ_SPECL           : term quotation list -> rule
  val Q_RESQ_HALF_ISPEC      : term quotation -> rule
  val Q_RESQ_HALF_ISPECL     : term quotation list -> rule
  val Q_RESQ_ISPEC           : term quotation -> rule
  val Q_RESQ_ISPECL          : term quotation list -> rule

end;
