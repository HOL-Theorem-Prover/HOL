(* =====================================================================*)
(* FILE          : cond_rewr.sig                                        *)
(* DESCRIPTION   : Signature for conditional rewriting conversions and  *)
(*                 tactics 					        *)
(* AUTHOR	 : P Curzon 					        *)
(* DATE		 : May 1993						*)
(*                                                                      *)
(* =====================================================================*)

signature Cond_rewrite =
sig
 type hol_type = Type.hol_type;
 type term     = Term.term
 type thm      = Thm.thm
 type tactic   = Abbrev.tactic
 type conv     = Abbrev.conv
 type thm_tactic = Abbrev.thm_tactic;

val COND_REWR_TAC :(term -> term -> 
                    ((term,term)Lib.subst * (hol_type,hol_type)Lib.subst) list)
                   -> thm_tactic
val search_top_down: term -> term -> 
                    ((term,term)Lib.subst * (hol_type,hol_type) Lib.subst) list
val COND_REWR_CANON: thm -> thm
val COND_REWRITE1_TAC: thm_tactic
val COND_REWR_CONV: (term -> term -> 
                     ((term,term)Lib.subst * (hol_type,hol_type)Lib.subst)list)
                    -> thm -> conv
val COND_REWRITE1_CONV: thm list -> thm -> conv
end;
