(* =====================================================================*)
(* FILE          : res_rules.sig                                        *)
(* DESCRIPTION   : Signature for restricted quantification inference    *)
(*                 rules 					        *)
(* AUTHOR	 : P Curzon 					        *)
(* DATE		 : May 1993						*)
(*                                                                      *)
(* =====================================================================*)

signature Res_quan =
sig
 type term     = Term.term
 type thm      = Thm.thm
 type tactic   = Abbrev.tactic
 type conv     = Abbrev.conv
 type thm_tactic = Abbrev.thm_tactic;

val mk_resq_forall: term * term * term -> term
val mk_resq_exists: term * term * term -> term
val mk_resq_select: term * term * term -> term
val mk_resq_abstract: term * term * term -> term
val list_mk_resq_forall: (term * term) list * term -> term
val list_mk_resq_exists: (term * term) list * term -> term
val dest_resq_forall: term -> term * term * term
val dest_resq_exists: term -> term * term * term
val dest_resq_select: term -> term * term * term
val dest_resq_abstract: term -> term * term * term
val strip_resq_forall: term -> (term * term) list * term
val strip_resq_exists: term -> (term * term) list * term
val is_resq_forall: term -> bool
val is_resq_exists: term -> bool
val is_resq_select: term -> bool
val is_resq_abstract: term -> bool
val RESQ_SPEC: term -> thm -> thm
val RESQ_SPECL: term list -> thm -> thm
val RESQ_SPEC_ALL: thm -> thm
val GQSPEC: term -> thm -> thm
val GQSPECL: term list -> thm -> thm
val GQSPEC_ALL: thm -> thm
val RESQ_HALF_SPEC: thm -> thm
val RESQ_HALF_EXISTS: thm -> thm
val RESQ_GEN: term * term -> thm -> thm
val RESQ_GENL: (term * term) list -> thm -> thm
val RESQ_GEN_ALL: thm -> thm
val RESQ_MATCH_MP: thm -> thm -> thm
val RESQ_HALF_GEN_TAC: tactic
val RESQ_GEN_TAC: tactic
val GGEN_TAC: tactic
val RESQ_EXISTS_TAC:  term -> tactic
val RESQ_IMP_RES_THEN: thm_tactic -> thm_tactic
val RESQ_RES_THEN: thm_tactic -> tactic
val RESQ_IMP_RES_TAC: thm_tactic
val RESQ_RES_TAC: tactic
val LHS_CONV: conv -> conv
val RHS_CONV: conv -> conv
val RF_BODY_CONV: conv -> conv
val RF_CONV: conv -> conv
val RESQ_FORALL_CONV: conv
val LIST_RESQ_FORALL_CONV: conv
val IMP_RESQ_FORALL_CONV: conv
val RESQ_FORALL_AND_CONV: conv
val AND_RESQ_FORALL_CONV: conv
val RESQ_FORALL_SWAP_CONV: conv
val RESQ_EXISTS_CONV: conv
val RESQ_REWR_CANON: thm -> thm
val RESQ_REWRITE1_TAC:  thm_tactic
val RESQ_REWRITE1_CONV:  thm list -> thm -> conv
val new_resq_definition: string * term -> thm
val new_infix_resq_definition: string * term * int -> thm
val new_binder_resq_definition: string * term -> thm
end;
