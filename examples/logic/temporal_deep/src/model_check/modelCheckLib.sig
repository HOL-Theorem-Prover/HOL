signature modelCheckLib =
sig

(*These lib is an interface to modelcheckers. The translationLib is
  used to translate several model checking problems to a check for the
  existance of a fair path through a kripke structure. Then a model checker
  is used to check these properties. At the moment SMV and temporalLib by
  Klaus Schneider are used. Thus, temporalLib has to work correctly, to
  make these lib work. Thus maker sure, the parameter smv_path of temporalLib
  has been ajusted to your systems and the examples for temporalLib work,
  before trying to use this lib.


  All functions return a thm option. If the specific property can be
  proved they return a theorem thm stating the property in the form
  SOME thm. If it can not be proved these functions print out a
  path showing a counterexample and return NONE.
*)

(*The file used to interact with smv*)
val model_check_temp_file : string ref;

val ctl_ks_fair2smv_string : Abbrev.term -> TextIO.outstream -> string
val fair_empty_ks2smv_string : Abbrev.term -> TextIO.outstream -> string

val model_check___ks_fair_emptyness : Abbrev.thm -> Abbrev.thm option
val modelCheckFairEmptyness : Abbrev.term -> Abbrev.thm -> bool


(*Checks that the given ltl-formula is a contradiction, i.e. that there
  is no path satisfing the formula*)
val model_check___ltl_contradiction : Abbrev.term -> Abbrev.thm option


(*Checks that the given ltl-formulas are equivalent at the first point of time. Since there are past ltl operators this does not mean that they are equivalent for all points of time!*)
val model_check___ltl_equivalent_initial : Abbrev.term -> Abbrev.term -> Abbrev.thm option

(*Checks that the given ltl-formulas are equivalent at all points of time.*)
val model_check___ltl_equivalent : Abbrev.term -> Abbrev.term -> Abbrev.thm option

(*model_check___ltl_ks_sem f M
checks that the given kripke_structure M models the ltl-formula f.
M has to be given in the form

symbolic_kripke_structure S0 R

where S0 and R may only contain, negations, conjunctions, disjuctions, implications and equivalences als boolean operators.*)
val model_check___ltl_ks_sem : Abbrev.term -> Abbrev.term -> Abbrev.thm option


(*Checks that the given sere and clock free PSL formula is a contradiction
  on infinite TOP and BOTTOM free paths, i.e. there is no
  infinite path that contains only "normal" states that fulfils the
  formula*)
val model_check___psl_contradiction : Abbrev.term -> Abbrev.thm option

(*Checks that the given sere and clock free PSL formulas are equivalent
  on infinite TOP and BOTTOM free paths*)
val model_check___psl_equivalent : Abbrev.term -> Abbrev.term -> Abbrev.thm option

(*Checks that the given sere and clock free PSL formulas is modeled by
  a kripke_structure.*)
val model_check___psl_ks_sem : Abbrev.term -> Abbrev.term -> Abbrev.thm option

end

