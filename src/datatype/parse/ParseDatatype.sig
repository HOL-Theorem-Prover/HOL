signature ParseDatatype =
sig

  datatype pretype =
    dVartype of string | dTyop of (string * pretype list) |
    dAQ of Type.hol_type
  type datatypeAST =
    string (* type name *) * ((string * pretype list) list)

   val parse : Type.hol_type frag list -> datatypeAST list

end;
