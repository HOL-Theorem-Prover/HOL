signature Datatype =
sig

 type hol_type = Type.hol_type
 type typeBase = TypeBase.typeBase
 type tyinfo = TypeBase.tyinfo
 type 'a quotation = 'a frag list;


 type tyspec = (hol_type * (string * hol_type list) list) list
   (* a list of type specifications; one for each type.  The first component
      is a type variable whose name (less the leading quote) is the name of
      the new type.  Each such is accompanied by a list of constructor
      specifications.  Such a spec. is a string (the constructor name) and
      a list of types that are the arguments of that constructor.
      Recursive occurrences of the types are marked by occurrences of the
      corresponding type variables. *)

 (* translates the parse datatype into a type specification, and also
    produces an accompanying list of "record information" for each
    type within the tyspec.  Record information is NONE for types that
    aren't records, and for those types that are, it is SOME of the list of
    field names *)
 val translate_parse :
   ParseDatatype.datatypeAST list -> (tyspec * string list option list)

 (* defines type(s) given a tyspec and returns a pair of the types'
    induction and recursion theorems, the latter is the type "Axiom" *)
 val raw_define_type : tyspec -> {induction: Thm.thm, recursion: Thm.thm}

 (* defines type(s), returns the tyinfo for each type, as well as the names
    of the extra theorems that have been added to the tyinfo as
    simplification theorems *)
 val define_type_from_parse :
   ParseDatatype.datatypeAST list -> (tyinfo * string list) list

 (* defines a size constant for a type *)
 val define_size_constant : typeBase -> tyinfo -> tyinfo


  (* A "pure" operation that doesn't write the underlying database of facts *)
  val primHol_datatype :
    typeBase -> hol_type quotation -> (tyinfo * string list) list

  (* Impure things *)

  (* arrange for a tyinfo to be written out to the theory file such
     that it will be read back into the TypeBase when the theory is
     loaded.  The list of strings is the list of names of any extra theorems
     in the simpls component of the tyinfo.  This means that the theorems
     to be added as extra simpls must have already been saved. *)
  val make_tyinfo_persist : (tyinfo * string list) -> unit

  val Hol_datatype : hol_type quotation -> unit

end;
