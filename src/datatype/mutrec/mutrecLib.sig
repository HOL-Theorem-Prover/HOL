signature mutrecLib =
sig
 type term = Term.term
 type fixity = Parse.fixity
 type thm = Thm.thm
 type 'a quotation = 'a frag list

 val define_type
     : {type_name : string,
	 constructors : {name:string,
                         arg_info : TypeInfo.type_info list}list}
        list
         ->
            {New_Ty_Existence      :thm,
             New_Ty_Induct         :thm,
             New_Ty_Uniqueness     :thm,
             Constructors_Distinct :thm,
             Constructors_One_One  :thm,
             Cases                 :thm,
             Argument_Extraction_Defs : (string * thm) list}

 val define_mutual_functions
     : {name:string,
        def : term,
        fixities : fixity list option,
        rec_axiom: thm} -> thm
end
