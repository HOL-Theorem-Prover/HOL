(*---------------------------------------------------------------------------*)
(* Regular expressions and a regexp matcher.                                 *)
(* Originated from Konrad Slind, tweaked by MJCG for Accellera PSL SEREs     *)
(* An automata-based matcher added by Joe Hurd                               *)
(*---------------------------------------------------------------------------*)

signature regexpTools =
sig

(******************************************************************************
* The trace levels of the regular expression library:
* 0: silent
* 1: 1 character (either - or +) for each list element processed
* 2: matches as they are discovered
* 3: transitions as they are calculated
* 4: internal state of the automata
******************************************************************************)

val EVAL_BIGLIST : Thm.thm -> Thm.thm list

(* Evaluating the Prefix operator on set regexps (like in Sugar) *)
val set_sat_conv : Abbrev.conv

(* Evaluating the Prefix operator on character regexps *)
val chr_sat_conv : Abbrev.conv

(* Set this to a SAT solver for evaluating the Prefix operator *)
val prefix_sat_conv : Abbrev.conv ref        (* by default = set_sat_conv *)

(* Exporting state machines
val export_dfa : Term.term list -> Term.term -> (int * bool * int list) list

val export_set_dfa :
  Term.term list -> Term.term ->
  (Term.term * bool) list list * (int * bool * int list) list
*)

datatype 'a condition =
  Leaf of 'a
| Branch of string * 'a condition * 'a condition

val extract_dfa :
  Term.term list -> Term.term ->
  (int * Term.term * (bool * Thm.thm) * (int * Thm.thm) condition) list

val LINE_LENGTH : int ref

val verilog_dfa :
  {name : string, alphabet : Term.term list, regexp : Term.term} -> string

end
