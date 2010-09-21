(* ===================================================================== *)
(* FILE          : numLib.sig                                            *)
(* DESCRIPTION   : useful proof support for :num.                        *)
(*                                                                       *)
(* ===================================================================== *)


signature numLib =
sig
 include numSyntax

 val EXISTS_LEAST_CONV        : conv
 val EXISTS_GREATEST_CONV     : conv
 val SUC_ELIM_CONV            : conv
 val SUC_TO_NUMERAL_DEFN_CONV : conv
 val num_CONV                 : conv

 val INDUCT_TAC               : tactic
 val completeInduct_on        : term quotation -> tactic
 val measureInduct_on         : term quotation -> tactic

 val LEAST_ELIM_TAC           : tactic

 val REDUCE_CONV              : conv
 val REDUCE_RULE              : thm -> thm
 val REDUCE_TAC               : tactic

 val ARITH_CONV               : conv
 val ARITH_PROVE              : conv
 val ARITH_TAC                : tactic

 val BOUNDED_FORALL_CONV      : conv -> conv
 val BOUNDED_EXISTS_CONV      : conv -> conv

 val std_ss                   : simpLib.simpset
 val arith_ss                 : simpLib.simpset

 val DECIDE                   : conv
 val DECIDE_TAC               : tactic

 val prefer_num               : unit -> unit
 val deprecate_num            : unit -> unit
end
