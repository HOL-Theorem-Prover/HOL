signature ConsThms =
sig
  type thm = Thm.thm

  val build : {New_Ty_Existence_Thm : thm, 
               New_Ty_Induct_Thm : thm,
               New_Ty_Uniqueness_Thm : thm}
              ->
                 {mutual_constructors_distinct : thm,
                  mutual_constructors_one_one : thm,
                  mutual_cases : thm,
                  argument_extraction_definitions : (string * thm) list}

end;
