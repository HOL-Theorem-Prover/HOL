signature RecordType =
sig

  val prove_recordtype_thms
    : TypeBasePure.tyinfo * string list -> TypeBasePure.tyinfo * string

  val update_tyinfo : Thm.thm list -> TypeBasePure.tyinfo ->
                      TypeBasePure.tyinfo
end

(*

   [prove_recordtype_thms] takes a tyinfo with the basic information
   about the type and a list of names for the record fields.  Returns
   a tyinfo and a string corresponding to an ML expression which modifies
   a tyinfo in the same way as the result has just been modified.

   [update_tyinfo ths] transforms a tyinfo by adding the ths to it as
   extra simplification theorems.

*)


