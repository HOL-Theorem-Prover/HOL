(* File: totoTacs.sig  Author: F.L.Morris created 8/20/12 *)

signature totoTacs =
sig

type conv = Abbrev.conv;
type thm = Thm.thm;
type term = Term.term;
type hol_type = Term.hol_type;
type tactic = Abbrev.tactic;

val PURE_MATCH_MP: thm -> thm -> thm;
val LESS_REWR: thm;
val EQUAL_REWR: thm;
val GREATER_REWR:thm;
val cpn_REWR_CONV: conv;

val toto_CONV: thm -> thm -> conv -> conv -> conv;
val numto_CONV: conv;
val charto_CONV: conv;
val qk_numto_CONV: conv;
val stringto_CONV: conv;
val intto_CONV: conv;

val lextoto_CONV: conv -> conv -> conv;
val listoto_CONV: conv -> conv;

end;
