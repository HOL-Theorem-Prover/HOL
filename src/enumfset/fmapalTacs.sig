(* File: fmapalTacs.sig  Author: F.L.Morris created 8/18/13 *)

signature fmapalTacs =
sig

type conv = Abbrev.conv;
type thm = Thm.thm;
type term = Term.term;
type hol_type = Term.hol_type;

val merge_CONV: conv -> conv;
val incr_sort_CONV: conv -> conv;

val fmap_TO_FMAPAL_CONV: conv -> term -> conv;
val FMAPAL_TO_fmap_CONV: conv -> conv;
val FUN_fmap_CONV: conv -> conv;
val FUN_FMAPAL_CONV: conv -> term -> conv -> conv;

val FAPPLY_CONV: conv -> conv;

val ORWL_TO_FMAPAL: thm -> thm;
val FMAPAL_TO_ORWL:conv -> conv;

val ORWL_FUNION: conv -> thm -> thm -> thm;
val FUNION_CONV: conv -> conv;

val ORWL_DRESTRICT: conv -> thm -> thm -> thm;
val ORWL_DRESTRICT_COMPL: conv -> thm -> thm -> thm;
val DRESTRICT_CONV: conv -> conv;

val MAP_ELEM_CONV: conv -> conv;
val FDOM_CONV: conv;
val IN_FDOM_CONV: conv -> conv;
val o_f_CONV: conv -> conv;

val FUPDATE_CONV: conv -> conv;

val FMAP_EXPR_CONV: conv -> conv;

end;
