signature ParseDatatype =
sig

   type datatypeAST =
     string (* type name *) *
     ((string * Type.hol_type parse_type.pretype list) list)

   val parse : Type.hol_type frag list -> datatypeAST list

end;
