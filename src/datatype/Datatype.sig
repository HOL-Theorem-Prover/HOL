signature Datatype =
sig

 type hol_type     = Type.hol_type
 type thm          = Thm.thm
 type tyinfo       = TypeBase.tyinfo
 type typeBase     = TypeBase.typeBase;
 type 'a quotation = 'a Portable.frag list
 type AST          = ParseDatatype.AST

 type field_name   = string
 type field_names  = string list
 type constructor  = string * hol_type list
 type tyspec       = hol_type * constructor list
 type record_rw_names = string list



 val define_type      : tyspec list -> {induction:thm, recursion:thm}
 val new_datatype     : hol_type quotation -> {induction:thm, recursion:thm}

 val build_tyinfos    : TypeBase.typeBase
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

 [xlate_parse] Translates the parsed datatype into a type specification, 
   and also produces an accompanying list of "record information" for each
   type within the tyspecs.  Record information is NONE for types that
   aren't records, and for those types that are, it is SOME of the list of
   field names.

 [raw_define_type]  Defines type(s) given a tyspecs and returns a pair
   of the types' induction and recursion theorems, the latter is the
   type "Axiom".

 [AST_datatype] Defines type(s), returns the tyinfo for each
   type, as well as the names of the extra theorems that have been added
   to the tyinfo as simplification theorems.

 [primHol_datatype] A "pure" operation that defines the type but doesn't 
   write the underlying database of facts.

 [make_tyinfo_persist] Arrange for a tyinfo to be written out to
    the theory file such that it will be read back into the TypeBase
    when the theory is loaded.  The list of strings is the list of names
    of any extra theorems in the simpls component of the tyinfo.  This
    means that the theorems to be added as extra simpls must have already
    been saved.

 [Hol_datatype] Define the type and write TypeBase.theTypeBase, and 
    arrange for the information about the type to be persistent.

*)

end;
