signature Tfl =
 sig
  type term   = Term.term
  type thm    = Thm.thm
  type tactic = Abbrev.tactic
  type thry   = TypeBase.typeBase

   datatype pattern = GIVEN of term * int
                    | OMITTED of term * int

   val mk_functional : thry -> term -> {functional:term, pats: pattern list}

   val read_context  : unit -> thm list
   val write_context : thm list -> unit

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

   type wfrec_eqns_result = {WFR : term, 
                             SV : term list,
                             proto_def : term,
                             extracta  : (thm * term list * bool) list,
                             pats : pattern list}

   val wfrec_eqns : thry -> term -> wfrec_eqns_result

   val lazyR_def : thry -> string -> wfrec_eqns_result 
                        -> {rules : thm,
                            R  : term,
                            SV : term list,
                            full_pats_TCs : (term * term list) list, 
                            patterns : pattern list,
                            theory : thry}

   val mk_induction : thry 
                       -> {fconst : term,
                           R : term,
                           SV : term list,
                           pat_TCs_list: (term * term list) list}
                       -> thm

   val postprocess: {WFtac:tactic, terminator:tactic, simplifier:term -> thm}
                    -> thry
                      -> {rules:thm, induction:thm, TCs:term list list}
                         -> {rules:thm, induction:thm, nested_tcs:thm list}

   val nested_function : thry -> string -> wfrec_eqns_result 
                        -> {rules:thm,ind:thm,SV:term list, R:term,
                            aux_rules:thm, aux_ind:thm,
                            theory:thry, def:thm,aux_def:thm}

   val mutual_function : thry -> string -> term 
                        -> {rules:thm, ind:thm, SV:term list, R:term,
                            union : {rules:thm, ind:thm, theory:thry,
                                     aux:{rules:thm, ind:thm}option},
                            theory:thry}

 end
