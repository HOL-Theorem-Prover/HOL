(* File: enumTacs.sig  Author: F.L.Morris created 8/17/13 *)

signature enumTacs =
sig

type conv = Abbrev.conv;
type thm = Thm.thm;
type term = Term.term;
type hol_type = Term.hol_type;

val EQ_LESS_CONV: conv;
val COND_EQ_LESS_CONV: conv;

val BL_CONS_CONV: conv;
val bt_rev_CONV: conv;

val bt_to_list_CONV: conv;
val bl_to_bt_CONV: conv;
val list_to_bl_CONV: conv;
val list_to_bt_CONV: conv;

val set_TO_ENUMERAL_CONV: conv -> term -> conv;
val DISPLAY_TO_set_CONV: conv;
val DISPLAY_TO_ENUMERAL_CONV:conv -> term -> conv;

val IN_CONV: conv -> conv;

val OWL_TO_ENUMERAL: thm -> thm;
val ENUMERAL_TO_OWL: conv -> conv;

val set_TO_DISPLAY_CONV: conv;
val ENUMERAL_TO_set_CONV: conv -> conv;
val ENUMERAL_TO_DISPLAY_CONV: conv -> conv;
val TO_set_CONV: conv -> conv;

val OWL_UNION: conv -> thm -> thm -> thm;
val UNION_CONV: conv -> conv;

val OWL_INTER: conv -> thm -> thm -> thm;
val INTER_CONV: conv -> conv;

val OWL_DIFF: conv -> thm -> thm -> thm;
val SET_DIFF_CONV: conv -> conv;

val SET_EXPR_TO_OWL: conv -> term -> thm;
val SET_EXPR_CONV: conv -> conv;

val set_TO_OWL: conv -> term -> term -> thm;

end;
