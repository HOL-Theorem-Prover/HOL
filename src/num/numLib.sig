(* ===================================================================== *)
(* FILE          : num_lib.sig  (Formerly num.sml)                       *)
(* DESCRIPTION   : Signature for useful proof support for :num.          *)
(*                                                                       *)
(* ===================================================================== *)


signature numLib = 
sig
  type thm = Thm.thm
  type conv = Abbrev.conv
  type tactic = Abbrev.tactic

 val EXISTS_LEAST_CONV    : conv
 val EXISTS_GREATEST_CONV : conv
 val SUC_ELIM_CONV : conv
 val num_CONV      : conv
 val INDUCT_TAC    : tactic

 val REDUCE_CONV : conv
 val REDUCE_RULE : thm -> thm
 val REDUCE_TAC  : tactic

 val ARITH_CONV  : conv 
 val ARITH_PROVE : conv
 val ARITH_TAC   : tactic

end;
