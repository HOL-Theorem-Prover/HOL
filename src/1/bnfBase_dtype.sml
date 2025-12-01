structure bnfBase_dtype =
struct

open Abbrev

datatype info = bI of {
  ty : hol_type,
  siblings : hol_type list,  (* types I'm mutually recursive with *)
  map : term * thm,          (* type's map term and its def'n thm *)
  set : term * thm,          (* type's set term and its def'n thm *)
  relator : term * thm,      (* type's rel term and its def'n thm *)
  bnd : term                 (* type's ordinal bnd term and its def'n thm *)
}


end
