signature Def_MN_Type =
 sig
   type 'a quotation = 'a frag list
   type hol_type = Type.hol_type
   type thm = Thm.thm

   val prim_define_type 
     : {type_name : string,
        constructors : {name : string,
                        arg_info : DefTypeInfo.type_info list} list} list
	-> thm list
        ->
	   {New_Ty_Existence_Thm: thm,
	    New_Ty_Induct_Thm : thm,
	    New_Ty_Uniqueness_Thm : thm,
	    Constructors_Distinct_Thm : thm,
	    Constructors_One_One_Thm : thm,
	    Cases_Thm : thm}

   val define_type 
     : thm list -> hol_type quotation
        ->
	   {New_Ty_Existence_Thm: thm,
	    New_Ty_Induct_Thm : thm,
	    New_Ty_Uniqueness_Thm : thm,
	    Constructors_Distinct_Thm : thm,
	    Constructors_One_One_Thm : thm,
	    Cases_Thm : thm}

   val string_define_type 
     : thm list -> string
        ->
	   {New_Ty_Existence_Thm: thm,
	    New_Ty_Induct_Thm : thm,
	    New_Ty_Uniqueness_Thm : thm,
	    Constructors_Distinct_Thm : thm,
	    Constructors_One_One_Thm : thm,
	    Cases_Thm : thm}

end;

