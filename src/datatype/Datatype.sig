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

 val big_record_size : int ref

 val tyspecs_of    : hol_type quotation -> tyspec list
 val to_tyspecs    : AST list -> tyspec list

 (*---------------------------------------------------------------------------*)
 (* Interfaces to the basic datatype definition package.                      *)
 (*---------------------------------------------------------------------------*)

 val define_type   : tyspec list -> {induction:thm, recursion:thm}
 val new_datatype  : hol_type quotation -> {induction:thm, recursion:thm}

 (*---------------------------------------------------------------------------*)
 (* A datatype declaration generates tyinfo data for each datatype declared.  *)
 (* The data of a tyinfo gets computed from the induction and recursion       *)
 (* for the type, and is stored in a TypeBase, usually TypeBase.theTypeBase.  *)
 (* Hol_datatype does this persistently; the other entrypoints support        *)
 (* variations.                                                               *)
 (* The string accompanying each tyinfo is the code for an ML expression      *)
 (* which will be of type tyinfo -> tyinfo.  This code can be inserted        *)
 (* into a theory file to update a datatype's basic tyinfo with extra         *)
 (* "smarts".  For example, record tyinfos get new rewrites to do obvious     *)
 (* things with fields and the like.  Big enumerated types, whose tyinfos     *)
 (* won't include a distinctness theorem, get an extra conversion stuffed     *)
 (* into their tyinfo to do inequality resolution.                            *)
 (*---------------------------------------------------------------------------*)

 val build_tyinfos : typeBase
                         -> {induction:thm, recursion:thm}
                           -> tyinfo list
 
 val write_tyinfos : (tyinfo * string) list -> unit

 val primHol_datatype : typeBase
                         -> AST list
                           -> typeBase * (tyinfo * string) list
 
 val astHol_datatype  : AST list -> unit
 val Hol_datatype  : hol_type quotation -> unit

end
