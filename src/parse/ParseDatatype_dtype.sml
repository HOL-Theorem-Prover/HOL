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

end
