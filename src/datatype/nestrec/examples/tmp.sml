local
    structure t0 : NestedRecTypeInputSig =
	struct
	    structure DefTypeInfo = DefTypeInfo
	    open DefTypeInfo
		
	    (* "Alist = mkA of Alist list" *)
		
	    val def_type_spec =
		[{type_name = "Alist",
		  constructors =
		  [{name = "mkA",
		    arg_info =
		    [type_op {Tyop = "list",
			      Args = [being_defined "Alist"]}]}]}]
	    val recursor_thms = [theorem "list" "list_Axiom"]
	    val New_Ty_Existence_Thm_Name = "t0_existence"
	    val New_Ty_Induct_Thm_Name = "t0_induct"
	    val New_Ty_Uniqueness_Thm_Name = "t0_unique"
	    val Constructors_Distinct_Thm_Name = "t0_distinct"
	    val Constructors_One_One_Thm_Name = "t0_one_one"
	    val Cases_Thm_Name = "t0_cases"
	end
in
    structure t0_Def = NestedRecTypeFunc (t0)
end;
