(* ===================================================================== *)
(* FILE          : num_lib.sig  (Formerly num.sml)                       *)
(* DESCRIPTION   : Signature for useful proof support for :num.          *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* ===================================================================== *)


signature numLib = 
sig
 val ADD_CONV : Abbrev.conv
 val num_EQ_CONV : Abbrev.conv
 val EXISTS_LEAST_CONV : Abbrev.conv
 val EXISTS_GREATEST_CONV : Abbrev.conv
 val num_CONV : Abbrev.conv
 val INDUCT_TAC : Abbrev.tactic
end;
