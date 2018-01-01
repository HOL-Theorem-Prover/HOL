structure ParseDatatype_dtype =
struct

 datatype pretype =
   dVartype of string
 | dTyop of {Tyop : string, Thy : string option, Args : pretype list}
 | dAQ of Type.hol_type

 type field       = string * pretype
 type constructor = string * pretype list

 datatype datatypeForm =
   Constructors of constructor list
 | Record of field list

 type AST = string * datatypeForm

 fun str s = "\"" ^ s ^ "\""
 fun pr (f1,f2) (a,b) = "(" ^ f1 a ^ "," ^ f2 b ^ ")"
 fun list_toString ef l = "[" ^ String.concatWith "," (map ef l) ^ "]"
 fun pt_toString pt =
   case pt of
       dVartype s => s
     | dTyop{Tyop,Thy,Args} =>
       let
         val thy = case Thy of NONE => "" | SOME s => s
       in
         thy ^ "$" ^ Tyop ^ list_toString pt_toString Args
       end
     | dAQ _ => "<AQ-type>"
 val c_toString = pr (str, list_toString pt_toString)
 val fld_toString = pr (str, pt_toString)
 fun dtF_toString dtf =
   case dtf of
       Constructors cl => "Constructors" ^ list_toString c_toString cl
     | Record fl => "Record" ^ list_toString fld_toString fl
 val toString = pr (str, dtF_toString)


end
