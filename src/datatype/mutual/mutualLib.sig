signature mutualLib =
sig
   type 'a quotation = 'a frag list
   type hol_type = Type.hol_type
   type fixity = Term.fixity
   type term = Term.term
   type thm = Thm.thm
   type tactic = Abbrev.tactic

   val define_type 
     : thm list -> hol_type quotation
        ->
	   {New_Ty_Existence_Thm: thm,
	    New_Ty_Induct_Thm : thm,
	    New_Ty_Uniqueness_Thm : thm,
	    Constructors_Distinct_Thm : thm,
	    Constructors_One_One_Thm : thm,
	    Cases_Thm : thm}

   val define_mutual_functions 
         :{name:string,
           def : term,
           fixities : fixity list option,
           rec_axiom: thm} -> thm


   val MUTUAL_INDUCT_THEN : thm -> (thm -> tactic) -> tactic

end