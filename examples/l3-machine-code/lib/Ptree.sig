(* -------------------------------------------------------------------------
   Ptree
   ------------------------------------------------------------------------- *)

signature Ptree =
sig
   type 'a ptree
   val Empty : 'a ptree
   val peek : 'a ptree * IntInf.int -> 'a option
   val add : 'a ptree * (IntInf.int * 'a) -> 'a ptree
   val transform : ('a -> 'b) -> 'a ptree -> 'b ptree
end
