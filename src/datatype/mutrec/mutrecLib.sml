structure mutrecLib :> mutrecLib =
struct

type thm = Thm.thm
type term = Term.term
type fixity= Parse.fixity
type 'a quotation = 'a frag list


 fun define_type input =
  let val (tmp as {New_Ty_Existence_Thm,
                   New_Ty_Induct_Thm,
                   New_Ty_Uniqueness_Thm}) = MutRecDef.define_type input
      val {mutual_constructors_distinct,
           mutual_constructors_one_one,
           mutual_cases,
           argument_extraction_definitions} = ConsThms.build tmp
  in
    {New_Ty_Existence = New_Ty_Existence_Thm,
     New_Ty_Induct = New_Ty_Induct_Thm,
     New_Ty_Uniqueness =  New_Ty_Uniqueness_Thm,
     Constructors_Distinct = mutual_constructors_distinct,
     Constructors_One_One = mutual_constructors_one_one,
     Cases = mutual_cases,
     Argument_Extraction_Defs = argument_extraction_definitions}
  end;

  val define_mutual_functions = Recftn.define_mutual_functions;

end;
