signature EquivType =
    sig
	val define_equivalence_type :
	    {name : string,
	     equiv : Thm.thm,
	     defs: {def_name:string, fname:string,
                    func:Term.term, fixity: Parse.fixity option} list,
	     welldefs : Thm.thm list,
	     old_thms : Thm.thm list}
	    -> Thm.thm list
    end
