signature RecordType =
sig

  (* takes a tyinfo with the basic information about the type and a
     list of names for the record fields.  Returns a tyinfo and a list
     of the names of the extra theorems that have been added to the
     tyinfo as simplifications *)

  val prove_recordtype_thms :
    TypeBase.TypeInfo.tyinfo * string list ->
    TypeBase.TypeInfo.tyinfo * string list
end
