signature Datatype =
sig
 type term = Term.term
 type hol_type = Type.hol_type
 type typeBase = TypeBase.typeBase
 type tyinfo = TypeBase.tyinfo
 type 'a quotation = 'a frag list;
 
  (* "Pure" operations that do not write the underlying database of facts *)

  val primHol_datatype : typeBase -> hol_type quotation -> tyinfo
  val type_size        : typeBase -> hol_type -> term


  (* An impure version *)

  val Hol_datatype : hol_type quotation -> unit
 
end;
