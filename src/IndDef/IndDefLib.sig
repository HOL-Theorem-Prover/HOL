signature IndDefLib =
sig
 type term = Term.term
 type thm = Thm.thm
 type tactic = Abbrev.tactic
 type thm_tactic = Abbrev.thm_tactic
 type monoset = (string * tactic) list


    val bool_monoset : monoset

    val gen_new_inductive_definition : monoset -> term -> (thm * thm * thm)

    val inductive_defn
        : monoset
          -> {name: string, fixity: Parse.fixity, patt: term*term list,
	      rules: {hypotheses : term list,side_conditions : term list,
		      conclusion: term} list}
	  -> thm * thm * thm

    val new_inductive_definition
	: {name: string, fixity: Parse.fixity, patt: term*term list,
	   rules: {hypotheses : term list,side_conditions : term list,
		   conclusion: term} list}
	-> thm * thm * thm

    val new_simple_inductive_definition : term list -> thm * thm * thm

    val RULE_INDUCT_THEN : thm -> thm_tactic -> tactic

    val prove_nonschematic_inductive_relations_exist : monoset -> term -> thm
    val derive_nonschematic_inductive_relations : term -> thm
    val prove_monotonicity_hyps : monoset -> thm -> thm
    val prove_inductive_relations_exist : monoset -> term -> thm

    val MONO_TAC : monoset -> tactic
    val BACKCHAIN_TAC : thm -> tactic

end;
