signature Pretype =
sig

   datatype 'a pretype 
        = tyVar   of 'a
        | tyAntiq of Type.hol_type
        | tyApp   of 'a * 'a pretype list;

   val pretype2type : ('a -> string) -> 'a pretype -> Type.hol_type

   type ground
   val name_of : ground -> string

   val prs_pretype 
     : int * (ground pretype list * Type.hol_type Strm.strm)
         -> ground pretype list * Type.hol_type Strm.strm

   val parse : Type.hol_type frag list -> ground pretype

end;
