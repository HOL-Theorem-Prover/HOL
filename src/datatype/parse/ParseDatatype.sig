signature ParseDatatype =
sig

  datatype pretype =
    dVartype of string | dTyop of (string * pretype list) |
    dAQ of Type.hol_type

  val pretypeToType : pretype -> Type.hol_type

  datatype datatypeForm =
    WithConstructors of ((string * pretype list) list) |
    RecordType of (string * pretype) list
  type datatypeAST = string (* type name *) * datatypeForm

   val parse : Type.hol_type frag list -> datatypeAST list

end;
