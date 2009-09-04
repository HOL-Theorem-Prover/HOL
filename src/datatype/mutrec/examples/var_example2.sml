new_theory "var_ex2";

load_library_in_place (find_library "mutrec");


structure test : MutRecTypeInputSig =
struct

structure TypeInfo = TypeInfo

open TypeInfo

(*
testa := empty_testa | cons_testa of testa testb
testb := contentb of 'leftopen testc
testc := connection of 'leftopentoo testa
*)

val mut_rec_ty_spec =[
  {type_name   ="testa",
   constructors=[
     {name    ="empty_testa",
      arg_info=[]
     },
     {name    ="cons_testa",
      arg_info=[being_defined "testb",
                being_defined "testa"]
     }
   ]
  },
  {type_name   ="testb",
   constructors=[
     {name    ="contentb",
      arg_info=[existing (==`:'leftopen`==),
                being_defined "testc"]
     }
   ]
  },
  {type_name   ="testc",
   constructors=[
     {name    ="connection",
      arg_info=[existing (==`:'leftopentoo`==),
                being_defined "testa"]
     }
   ]
  }
]

    val New_Ty_Existence_Thm_Name = "var_ex2_existence_thm"
    val New_Ty_Induct_Thm_Name = "var_ex2_induction_thm"
    val New_Ty_Uniqueness_Thm_Name = "var_ex2_uniqueness_thm"
    val Constructors_One_One_Thm_Name = "var_ex2_constructors_one_one"
    val Constructors_Distinct_Thm_Name = "var_ex2_constructors_distinct"
    val Cases_Thm_Name = "var_ex2_cases"


end; (* struct *)

structure test_Def = MutRecTypeFunc (test);


val more_empty_DEF = define_mutual_functions
{name = "more_empty_DEF",
 rec_axiom = var_ex2_existence_thm,
 fixities = SOME [(Infix 600), Prefix, Prefix],
 def =
(--`(more_empty (empty_testa:('x,'y)testa) = \a:('x,'y)testa. F) /\
    (more_empty (cons_testa b a) = \aa.
     ((aa = empty_testa) \/
      (bmore_empty b (cons_testa_arg1 aa) /\
       more_empty a (cons_testa_arg2 aa)))) /\
    (bmore_empty (contentb (x:'x) c) = \b:('x,'y)testb.
     cmore_empty c (contentb_arg2 b)) /\
    (cmore_empty (connection (y:'y) a) = \c:('x,'y)testc.
     more_empty a (connection_arg2 c))`--)};

(*
val more_empty_DEF =
  |- ($more_empty empty_testa = (\a. F)) /\
     (!x1 x2.
       $more_empty (cons_testa x1 x2) =
       (\aa.
         (aa = empty_testa) \/
         bmore_empty x1 (cons_testa_arg1 aa) /\
         x2 more_empty cons_testa_arg2 aa)) /\
     (!x1 x2.
       bmore_empty (contentb x1 x2) =
       (\b. cmore_empty x2 (contentb_arg2 b))) /\
     (!x1 x2.
       cmore_empty (connection x1 x2) = (\c. x2 more_empty connection_arg2 c))
  : thm
*)
