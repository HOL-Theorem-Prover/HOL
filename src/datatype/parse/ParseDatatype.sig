signature ParseDatatype =
sig

   type datatypeAST 
         = string       (* type name *)
           * ((string * Pretype.ground Pretype.pretype list) list)

   val rawparse : Type.hol_type Strm.strm
                  -> datatypeAST list * Type.hol_type Strm.strm

   val parse : Type.hol_type frag list -> datatypeAST list

end;
