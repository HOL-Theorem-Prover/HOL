val _ = new_theory "test";

val _ = load_library_in_place (find_library "mutrec");

structure test : MutRecTypeInputSig =
struct

structure TypeInfo = TypeInfo

open TypeInfo

val mut_rec_ty_spec =
    [{type_name = "toto",
      constructors=[{name ="empty_test", arg_info=[]}]}]
val New_Ty_Existence_Thm_Name = "toto_existence_thm"
val New_Ty_Induct_Thm_Name = "toto_induction_thm"
val New_Ty_Uniqueness_Thm_Name = "toto_uniqueness_thm"
val Constructors_One_One_Thm_Name = "toto_constructors_one_one"
val Constructors_Distinct_Thm_Name = "toto_constructors_distinct"
val Cases_Thm_Name = "toto_cases"

end; (* struct *)

structure test_Def = MutRecTypeFunc (test);



structure test1 : MutRecTypeInputSig =
struct

structure TypeInfo = TypeInfo

open TypeInfo

val mut_rec_ty_spec =
    [{type_name = "toto1",
      constructors=[{name ="test1", arg_info=[existing(==`:'a`==)]},
		    {name ="test2", arg_info=[existing(==`:'b`==)]}]},
     {type_name = "tutu1",
      constructors=[{name ="test3", arg_info=[]}]}]
val New_Ty_Existence_Thm_Name = "toto1_existence_thm"
val New_Ty_Induct_Thm_Name = "toto1_induction_thm"
val New_Ty_Uniqueness_Thm_Name = "toto1_uniqueness_thm"
val Constructors_Distinct_Thm_Name = "toto1_constructors_distinct"
val Constructors_One_One_Thm_Name = "toto1_constructors_one_one"
val Cases_Thm_Name = "toto1_cases"

end; (* struct *)


structure test1_Def = MutRecTypeFunc (test1);
