(* ===================================================================== *)
(* FILE          : utilsLib.sig                                         *)
(* DESCRIPTION   : Signature for a structure of general-purpose theorem  *)
(*                 proving routines, used in the "group" library.        *)
(*                 Translated and improved from the hol88 implementation.*)
(*                                                                       *)
(* AUTHOR        : Elsa Gunter, Bell Labs                                *)
(* DATE          : January 5, 1992                                       *)
(* ===================================================================== *)
(* Copyright 1992 by AT&T Bell Laboratories *)
(* Share and Enjoy *)



signature elsaUtils =
sig
type hol_type = Type.hol_type;
type term = Term.term
type thm = Thm.thm
type tactic = Abbrev.tactic
type conv = Abbrev.conv
type thm_tactic = Abbrev.thm_tactic;


  val ADD_ASSUMS_THEN :{new_assumptions:term list, tactic:tactic} -> tactic
  val ADD_STRIP_ASSUMS_THEN :{new_assumptions:term list, tactic:tactic} ->
                             tactic
  val ASM_CONJ1_TAC :tactic
  val ASM_CONJ2_TAC :tactic
  val ASSUME_LIST_TAC :thm list -> tactic
  val AUTO_SPEC :{generalized_theorem:thm, specialization_term:term} -> thm
  val AUTO_SPECL :{generalized_theorem:thm,
                   specialization_list:term list} -> thm
  val MATCH_MP_IMP_TAC :thm_tactic
  val MATCH_TERM_SUBS_RULE :thm -> term -> thm -> thm
  val MATCH_THM_TAC :{pattern_function:term -> term, thm_tactic:thm_tactic} ->
                     thm_tactic
  val MP_IMP_TAC :thm_tactic
  val NEW_MATCH_ACCEPT_TAC :thm_tactic
  val NEW_SUBST1_TAC :thm_tactic
  val REDUCE_TAC :thm list -> tactic
  val REV_SUPPOSE_TAC :term -> tactic
  val STRONG_INST :{term_substitution:(term,term)Lib.subst, theorem:thm} -> thm
  val STRONG_INST_TYPE
      :{theorem:thm,type_substitution:(hol_type,hol_type) Lib.subst} -> thm
  val STRONG_INST_TY_TERM :{term_substitution:(term,term) Lib.subst,
                            theorem:thm,
                            type_substitution:(hol_type,hol_type)Lib.subst} -> 
                           thm
  val SUBST_MATCH_TAC :thm_tactic
  val SUPPOSE_TAC :term -> tactic
  val find_match :{pattern:term, term:term} 
                   -> (term,term) Lib.subst * (hol_type,hol_type) Lib.subst
  val is_contained_in :{subset:term list, superset: term list} -> bool
  val mapshape :{functions:('a list -> 'b) list,
                 partition:int list,
                 unionlist:'a list} -> 'b list
  val use_thm :{theorem:thm, thm_tactic:thm_tactic} -> tactic
end
