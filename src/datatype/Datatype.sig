signature Datatype =
sig

 include Abbrev
 type tyinfo       = TypeBasePure.tyinfo
 type typeBase     = TypeBasePure.typeBase;
 type AST          = ParseDatatype.AST

 type field_name   = string
 type field_names  = string list
 type constructor  = string * hol_type list
 type tyspec       = hol_type * constructor list
 type record_rw_names = string list



 val define_type      : tyspec list -> {induction:thm, recursion:thm}
 val new_datatype     : hol_type quotation -> {induction:thm, recursion:thm}

 val build_tyinfos    : typeBase
                         -> {induction:thm, recursion:thm}
                           -> tyinfo list

 val primHol_datatype : typeBase
                           -> hol_type quotation
                             -> (tyinfo * record_rw_names) list

 val write_tyinfo     : tyinfo * record_rw_names -> unit

 val Hol_datatype     : hol_type quotation -> unit

(*---------------------------------------------------------------------------

 [tyspec] A type specification.  The first component is a type variable
   whose name (less the leading quote) is the name of the new type.  Each
   such is accompanied by a list of constructor specifications.  Such a
   spec. is a string (the constructor name) and a list of types that are
   the arguments of that constructor. Recursive occurrences of the types
   are marked by occurrences of the corresponding type variables.

 [primHol_datatype] A "pure" operation that defines the type but doesn't
   write the underlying database of facts.

 [Hol_datatype] Define the type and write TypeBase.theTypeBase, and
    arrange for the information about the type to be persistent.

*)

end;
