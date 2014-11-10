(* File: tcTacs.sig  Author: F.L.Morris created 9/6/13 *)

signature tcTacs =
sig

type conv = Abbrev.conv;
type thm = Thm.thm;
type term = Term.term;
type hol_type = Term.hol_type;

val FMAP_TO_RELN: thm;

val ENUF_CONV: conv -> term -> conv;

val TC_CONV: conv -> conv;



end;
