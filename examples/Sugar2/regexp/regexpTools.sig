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

(* For evaluating the Prefix operator on set regexps *)
val set_sat_conv : Abbrev.conv

(* For evaluating the Prefix operator on character regexps *)
val chr_sat_conv : Abbrev.conv

(* Set this to a SAT solver for evaluating the Prefix operator *)
val prefix_sat_conv : Abbrev.conv ref        (* by default = set_sat_conv *)

end
