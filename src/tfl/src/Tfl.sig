signature Tfl =
 sig
  type term = Term.term
  type thm   = Thm.thm
  type tactic = Abbrev.tactic
  type thry = Thry.thry

   datatype pattern = GIVEN of term * int
                    | OMITTED of term * int

   val mk_functional : thry -> term -> {functional:term, pats: pattern list}

   val prim_wfrec_definition : 
        thry -> string 
             -> {R:term, functional:term}
             -> {def:thm, corollary:thm, theory:thry}

   val gen_wfrec_definition : 
         thry -> string
              -> {R:term, eqs:term}
              -> {rules:thm, 
                  TCs: term list list,
                  full_pats_TCs: (term * term list) list,
                  patterns :pattern list,
                  theory:thry}

   val wfrec_eqns : thry -> term 
                         -> {WFR : term, 
                             proto_def : term,
                             extracta  : (thm * term list) list,
                             pats  : pattern list}

   val lazyR_def : thry -> string -> term 
                        -> {rules:thm,
                            R : term,
                            full_pats_TCs:(term * term list) list, 
                            patterns: pattern list,
                            theory:thry}

   val mk_induction : thry -> term -> term -> (term * term list) list -> thm

   val postprocess: {WFtac:tactic, terminator:tactic, simplifier:term -> thm}
                    -> thry
                      -> {rules:thm, induction:thm, TCs:term list list}
                         -> {rules:thm, induction:thm, nested_tcs:thm list}

   val termination_goals : thm -> term list
 end
