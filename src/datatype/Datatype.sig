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

end
