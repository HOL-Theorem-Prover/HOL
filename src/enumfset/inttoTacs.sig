(* File: inttoTacs.sig  Author: F.L.Morris created 12/13/13 *)

signature inttoTacs =
sig

type conv = Abbrev.conv;
type thm = Thm.thm;
type term = Term.term;
type hol_type = Term.hol_type;
type tactic = Abbrev.tactic;

val intto_CONV: conv;

end;
